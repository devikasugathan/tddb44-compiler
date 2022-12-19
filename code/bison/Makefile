bison:
	bison --version || $(MAKE) bison-build

bison-3.8.tar.xz:
	wget -O "$@" https://ftp.gnu.org/gnu/bison/bison-3.8.tar.xz
bison-build: bison-3.8.tar.xz
	tar xJvf "$<"
	cd bison-3.8 && ./configure --prefix $(PWD)
	$(MAKE) -C bison-3.8
	$(MAKE) -C bison-3.8 install
