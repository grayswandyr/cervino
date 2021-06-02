PACKAGES="ubuntu-desktop virtualbox-guest-x11 firefox evince emacs gedit"

sudo apt-get install -y --no-install-recommends $PACKAGES

# autologin

sudo sed -i 's_#  Auto_Auto_; s_user1_vagrant_' /etc/gdm3/custom.conf

# shell

gsettings set org.gnome.shell favorite-apps "['firefox.desktop', 'org.gnome.Nautilus.desktop', 'org.gnome.Terminal.desktop']"

GNOME_TERMINAL_PROFILE=`gsettings get org.gnome.Terminal.ProfilesList default | awk -F \' '{print $2}'`
gsettings set org.gnome.Terminal.Legacy.Profile:/org/gnome/terminal/legacy/profiles:/:$GNOME_TERMINAL_PROFILE/ font 'Monospace 12'
gsettings set org.gnome.Terminal.Legacy.Profile:/org/gnome/terminal/legacy/profiles:/:$GNOME_TERMINAL_PROFILE/ use-system-font false