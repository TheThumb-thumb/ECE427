name = trivium
type = sync

root = $(ECRYPT_ROOT)
api = ecrypt-$(type).h

ifdef STD
  std = $(STD)
else
  std = -ansi
endif

ifdef OPT
  opt = $(OPT)
else
  opt = -O3
endif

CFLAGS = -Wall -pedantic $(opt) $(std) 
CPPFLAGS = -DECRYPT_API=$(api) -I $(root)/include -I .
VPATH = $(root)/test:$(root)/api:$(root)/include

ecrypt-test: ecrypt-test.o ecrypt-$(type).o $(name).o

$(api): ecrypt-config.h ecrypt-machine.h ecrypt-portable.h 

ecrypt-test.o: $(api)
ecrypt-$(type).o: $(api)

$(name).o: $(api)

clean:
	$(RM) ecrypt-test *.o
