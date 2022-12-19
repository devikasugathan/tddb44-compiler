flex:
	flex --version || $(MAKE) flex-build

flex-2.6.4.tar.gz:
	wget -O "$@" https://github.com/westes/flex/files/981163/flex-2.6.4.tar.gz
flex-build: flex-2.6.4.tar.gz
	tar xzvf "$<"
	cd flex-2.6.4 && ./configure --prefix $(PWD)
	$(MAKE) -C flex-2.6.4
	$(MAKE) -C flex-2.6.4 install
