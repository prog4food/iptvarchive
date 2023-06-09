#!/bin/sh
# Extract: dpkg-deb -R <file>.ipk
BDIR=.
PKG=enigma2-plugin-extensions-iptvarchive_2.0.3_all_foss

# Pre clean
rm -r "$BDIR/${PKG}.ipk" > /dev/null 2>&1
# Build
dpkg-deb -Zgzip -b "$BDIR/ipk"
# Convert to ar
ar xo "$BDIR/ipk.deb"
ar rUov "$BDIR/${PKG}.ipk" "$BDIR/debian-binary" "$BDIR/control.tar.gz" "$BDIR/data.tar.gz"
mv "$BDIR/ipk.deb" "$BDIR/${PKG}.deb"
# Clean
rm "$BDIR/debian-binary" "$BDIR/control.tar.gz" "$BDIR/data.tar.gz"
