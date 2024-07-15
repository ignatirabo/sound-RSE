.PHONY:	all test

SRC := src
EXE := main.exe
DUNECLEAN := dune clean
DUNEBUILD := dune build
DUNEROOT := --root $(SRC)

all: build ln

build:
	$(DUNEBUILD) $(DUNEROOT) $(EXE)

ln:
	ln -fs $(SRC)/_build/default/main.exe $(EXE)

test:
	$(DUNEBUILD) $(DUNEROOT) --force --display short @test

clean:
	$(DUNECLEAN) $(DUNEROOT)
	rm -f $(EXE)
