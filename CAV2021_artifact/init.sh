PACKAGES="virtualbox-guest-dkms virtualbox-guest-utils git wget build-essential autoconf"

echo '********************************************************************************'
printf "Running: init.sh\n" 
echo '********************************************************************************'

apt-get update
apt-get upgrade

apt-get install -y --no-install-recommends $PACKAGES