// Patches KeyboardManager._lastDeviceIsTouchscreen so _syncEnabled()'s
// autoEnabled term is false outside shell modals. The OSK then appears only
// in modals or when org.gnome.desktop.a11y.applications screen-keyboard-enabled
// is true -- a clean, reversible off-switch GNOME doesn't otherwise offer.
import * as Main from 'resource:///org/gnome/shell/ui/main.js';

export default class NoAutoOsk {
    enable() {
        this._orig = Main.keyboard._lastDeviceIsTouchscreen;
        // Shell modals (polkit password dialogs) grab all input, so touchkbd
        // can't be tapped there -- let the built-in OSK auto-show only then.
        Main.keyboard._lastDeviceIsTouchscreen = () => Main.modalCount > 0;
        Main.keyboard._syncEnabled();
    }

    disable() {
        if (this._orig) {
            Main.keyboard._lastDeviceIsTouchscreen = this._orig;
            this._orig = null;
        }
        Main.keyboard._syncEnabled();
    }
}
