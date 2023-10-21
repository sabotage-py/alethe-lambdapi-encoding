.POSIX:
SRC = $(wildcard *.lp)
OBJ = $(SRC:.lp=.lpo)
.SUFFIXES:

LAMBDAPI = lambdapi

all: 
	$(LAMBDAPI) check $(SRC)

install: $(OBJ) lambdapi.pkg
	lambdapi install lambdapi.pkg $(OBJ) $(SRC)

uninstall:
	lambdapi uninstall lambdapi.pkg

clean:
	rm -f $(OBJ)

.SUFFIXES: .lp .lpo

.lp.lpo:
	lambdapi check --gen-obj $<
