use std::ffi::{CStr, CString};
use super::Control;
use callback_helpers::{from_void_ptr, to_heap_ptr};
use std::i32;
use std::mem;
use std::os::raw::c_void;
use str_tools::to_toolkit_string;
use ui::UI;
use libui_ffi::{self, uiCheckbox, uiControl};

define_control! {
    /// Boolean selection control which can be checked or unchecked.
    rust_type: Checkbox,
    sys_type: uiCheckbox
}

impl Checkbox {
    // Create a new Checkbox which can produce values from `min` to `max`.
    pub fn new(text: &str) -> Self {
        let c_string = to_toolkit_string(text);
        unsafe { Checkbox::from_raw(libui_ffi::uiNewCheckbox(c_string.as_ptr())) }
    }

    pub fn checked(&self) -> bool {
        unsafe { libui_ffi::uiCheckboxChecked(self.uiCheckbox) != 0 }
    }

    pub fn set_checked(&mut self, checked: bool) {
        unsafe { libui_ffi::uiCheckboxSetChecked(self.uiCheckbox, checked as i32) }
    }

    pub fn on_toggled<'ctx, F>(&mut self, _ctx: &'ctx UI, callback: F)
    where
        F: FnMut(bool) + 'static,
    {
        extern "C" fn c_callback<G>(checkbox: *mut uiCheckbox, data: *mut c_void)
        where
            G: FnMut(bool),
        {
            let val = unsafe { libui_ffi::uiCheckboxChecked(checkbox) } != 0;
            unsafe { from_void_ptr::<G>(data)(val) }
        }

        unsafe {
            libui_ffi::uiCheckboxOnToggled(
                self.uiCheckbox,
                Some(c_callback::<F>),
                to_heap_ptr(callback),
            );
        }
    }

    /// Get a copy of the existing text on the checkbox.
    pub fn text(&self) -> String {
        unsafe {
            CStr::from_ptr(libui_ffi::uiCheckboxText(self.uiCheckbox))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Get a reference to the existing text on the checkbox.
    pub fn text_ref(&self) -> &CStr {
        unsafe { CStr::from_ptr(libui_ffi::uiCheckboxText(self.uiCheckbox)) }
    }

    /// Set the text label on the checkbox
    pub fn set_text(&mut self, text: &str) {
        unsafe {
            let c_string = CString::new(text.as_bytes().to_vec()).unwrap();
            libui_ffi::uiCheckboxSetText(self.uiCheckbox, c_string.as_ptr())
        }
    }
}
