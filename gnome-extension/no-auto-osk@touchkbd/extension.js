// Patches KeyboardManager._lastDeviceIsTouchscreen to return false, so
// _syncEnabled()'s autoEnabled term is always false. The OSK then appears
// only when org.gnome.desktop.a11y.applications screen-keyboard-enabled
// is true -- a clean, reversible off-switch GNOME doesn't otherwise offer.
import * as Main from 'resource:///org/gnome/shell/ui/main.js';

export default class NoAutoOsk {
    enable() {
        this._orig = Main.keyboard._lastDeviceIsTouchscreen;
        Main.keyboard._lastDeviceIsTouchscreen = () => false;
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
