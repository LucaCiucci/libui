use callback_helpers::{from_void_ptr, to_heap_ptr};
use error::UIError;
use ffi_tools;
use std::os::raw::{c_int, c_void};
use libui_ffi;

use std::ffi::CStr;
use std::marker::PhantomData;
use std::mem;
use std::rc::Rc;
use std::sync::{Arc, RwLock};
use std::thread;
use std::time::{Duration, SystemTime};

use controls::Window;

/// RAII guard for the UI; when dropped, it uninits libUI.
struct UIToken {
    // This PhantomData prevents UIToken from being Send and Sync
    _pd: PhantomData<*mut ()>,
    initialized: Arc<RwLock<bool>>
}

impl UIToken {
    fn new() -> Self {
        Self {
            _pd: PhantomData,
            initialized: Arc::new(RwLock::new(true))
        }
    }
}

impl Drop for UIToken {
    fn drop(&mut self) {
        assert!(
            ffi_tools::is_initialized(),
            "Attempted to uninit libUI in UIToken destructor when libUI was not initialized!"
        );
        *self.initialized.write().unwrap() = false;
        unsafe {
            Window::destroy_all_windows();
            libui_ffi::uiUninit();
            ffi_tools::unset_initialized();
        }
    }
}

/// A handle to user interface functionality.
#[derive(Clone)]
pub struct UI {
    _token: Rc<UIToken>,
}

impl UI {
    /// Initializes the underlying UI bindings, producing a [`UI`](struct.UI.html) struct which can be used
    /// to actually build your user interface. This is a reference counted type; clone it
    /// to get an additional reference that can be passed to, e.g., callbacks.
    ///
    /// Only one libUI binding can be active at once; if multiple instances are detected,
    /// this function will return a [`MultipleInitError`](enum.UIError.html#variant.MultipleInitError).
    /// Be aware the Cocoa (GUI toolkit on Mac OS) requires that the _first thread spawned_ controls
    /// the UI, so do _not_ spin off your UI interactions into an alternative thread. You're likely to
    /// have problems on Mac OS.
    ///
    /// ```no_run
    /// # use libui::UI;
    /// {
    ///     let ui1 = UI::init().unwrap();
    ///
    ///     // This will fail because there is already an instance of UI.
    ///     let ui2 = UI::init();
    ///     assert!(ui2.is_err());
    ///
    ///     // ui1 dropped here.
    /// }
    /// let ui3 = UI::init().unwrap();
    /// ```
    ///
    /// If libUI cannot initialize its hooks into the platform bindings, this function will
    /// return a [`FailedInitError`](enum.UIError.html#variant.FailedInitError) with the description of the problem.
    pub fn init() -> Result<UI, UIError> {
        if ffi_tools::is_initialized() {
            return Err(UIError::MultipleInitError {});
        };

        unsafe {
            // Create the magic value needed to init libUI
            let mut init_options = libui_ffi::uiInitOptions {
                Size: mem::size_of::<libui_ffi::uiInitOptions>(),
            };

            // Actually start up the library's functionality
            let err = libui_ffi::uiInit(&mut init_options);
            if err.is_null() {
                // Success! We can safely give the user a token allowing them to do UI things.
                ffi_tools::set_initialized();
                Ok(UI {
                    _token: Rc::new(UIToken::new()),
                })
            } else {
                // Error occurred; copy the string describing it, then free that memory.
                let error_string = CStr::from_ptr(err).to_string_lossy().into_owned();
                libui_ffi::uiFreeInitError(err);
                Err(UIError::FailedInitError {
                    error: error_string,
                })
            }
        }
    }

    /// Hands control of this thread to the UI toolkit, allowing it to display the UI and respond to events.
    /// Does not return until the UI [quit](struct.UI.html#method.quit)s.
    ///
    /// For more control, use the `EventLoop` struct.
    pub fn main(&self) {
        self.event_loop().run();
    }

    /// Returns an `EventLoop`, a struct that allows you to step over iterations or events in the UI.
    pub fn event_loop(&self) -> EventLoop {
        unsafe { libui_ffi::uiMainSteps() };
        return EventLoop {
            _pd: PhantomData,
            callback: None,
        };
    }

    /// Returns an `EventQueue`, a struct that allows you to queue closure from other threads
    pub fn event_queue(&self) -> EventQueue {
        EventQueue {
            initialized: self._token.initialized.clone(),
        }
    }

    /// Running this function causes the UI to quit, exiting from [main](struct.UI.html#method.main) and no longer showing any widgets.
    ///
    /// Run in every window's default `on_closing` callback.
    pub fn quit(&self) {
        unsafe { libui_ffi::uiQuit() }
    }

    /// Queues a function to be executed on the GUI thread when next possible. Returns
    /// immediately, not waiting for the function to be executed.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use libui::prelude::*;
    ///
    /// let ui = UI::init().unwrap();
    ///
    /// ui.queue_main(|| { println!("Runs first") } );
    /// ui.queue_main(|| { println!("Runs second") } );
    /// ui.quit();
    /// ```
    pub fn queue_main<F: FnMut() + 'static>(&self, callback: F) {
        extern "C" fn c_callback<G: FnMut()>(data: *mut c_void) {
            unsafe {
                from_void_ptr::<G>(data)();
            }
        }

        unsafe {
            libui_ffi::uiQueueMain(Some(c_callback::<F>), to_heap_ptr(callback));
        }
    }

    /// Set a callback to be run when the application quits.
    pub fn on_should_quit<F: FnMut() + 'static>(&self, callback: F) {
        extern "C" fn c_callback<G: FnMut()>(data: *mut c_void) -> i32 {
            unsafe {
                from_void_ptr::<G>(data)();
                0
            }
        }

        unsafe {
            libui_ffi::uiOnShouldQuit(Some(c_callback::<F>), to_heap_ptr(callback));
        }
    }
}

/// Provides fine-grained control over the user interface event loop, exposing the `on_tick` event
/// which allows integration with other event loops, custom logic on event ticks, etc.
/// Be aware the Cocoa (GUI toolkit on Mac OS) requires that the _first thread spawned_ controls
/// the UI, so do _not_ spin off your UI interactions into an alternative thread. You're likely to
/// have problems on Mac OS.

pub struct EventLoop<'s> {
    // This PhantomData prevents UIToken from being Send and Sync
    _pd: PhantomData<*mut ()>,
    // This callback gets run during "run_delay" loops.
    callback: Option<Box<dyn FnMut() + 's>>,
}

impl<'s> EventLoop<'s> {
    /// Set the given callback to run when the event loop is executed.
    /// Note that if integrating other event loops you should consider
    /// the potential benefits and drawbacks of the various run modes.
    pub fn on_tick<'ctx, F: FnMut() + 's + 'ctx>(&'ctx mut self, callback: F) {
        self.callback = Some(Box::new(callback));
    }

    /// Executes a tick in the event loop, returning immediately.
    /// The `on_tick` callback is executed after the UI step.
    ///
    /// Returns `true` if the application should continue running, and `false`
    /// if it should quit.
    pub fn next_tick(&mut self) -> bool {
        let result = unsafe { libui_ffi::uiMainStep(false as c_int) == 1 };
        if let Some(ref mut c) = self.callback {
            c();
        }
        result
    }

    /// Hands control to the event loop until the next UI event occurs.
    /// The `on_tick` callback is executed after the UI step.
    ///
    /// Returns `true` if the application should continue running, and `false`
    /// if it should quit.
    pub fn next_event_tick(&mut self) -> bool {
        let result = unsafe { libui_ffi::uiMainStep(true as c_int) == 1 };
        if let Some(ref mut c) = self.callback {
            c();
        }
        result
    }

    /// Hands control to the event loop until [`UI::quit()`](struct.UI.html#method.quit) is called,
    /// running the callback given with `on_tick` after each UI event.
    pub fn run(&mut self) {
        loop {
            if !self.next_event_tick() {
                break;
            }
        }
    }

    /// Hands control to the event loop until [`UI::quit()`](struct.UI.html#method.quit) is called,
    /// running the callback given with `on_tick` approximately every
    /// `delay` milliseconds.
    pub fn run_delay(&mut self, delay_ms: u32) {
        if let Some(ref mut c) = self.callback {
            let delay_ms = delay_ms as u128;
            let mut t0 = SystemTime::now();
            'event_loop: loop {
                for _ in 0..5 {
                    if !unsafe { libui_ffi::uiMainStep(false as c_int) == 1 } {
                        break 'event_loop;
                    }
                }
                if let Ok(duration) = t0.elapsed() {
                    if duration.as_millis() >= delay_ms {
                        c();
                        t0 = SystemTime::now();
                    }
                } else {
                    t0 = SystemTime::now();
                }
                thread::sleep(Duration::from_millis(5));
            }
        } else {
            self.run()
        }
    }
}

/// The struct to enqueue a closure from another thread
pub struct EventQueue {
    initialized: Arc<RwLock<bool>>,
}

impl EventQueue {
    /// Tries to enqueue the callback to event queue for the main thread
    /// 
    /// Returns false if the `UI` is already dropped and unable to queue the event.
    pub fn queue_main<F: FnMut() + 'static + Send>(&self, callback: F) -> bool {
        let initialized = self.initialized.read().unwrap();

        if !*initialized {
            return false;
        }

        extern "C" fn c_callback<G: FnMut()>(data: *mut c_void) {
            unsafe {
                from_void_ptr::<G>(data)();
            }
        }

        unsafe {
            libui_ffi::uiQueueMain(Some(c_callback::<F>), to_heap_ptr(callback));
        }

        true
    }
}
