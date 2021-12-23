# This uses Madoko (https://madoko.codeplex.com/)

STUFF=fstarlang.json script.js style.css latex.tex fstar-new.png Billions.png Dsls.png

OUT=out/VeriCrypt2021

all: prep
	madoko --pedantic vericrypt-fstar-overview.mdk --odir=$(OUT)

prep:
	mkdir -p $(OUT)/aux
	cp $(addprefix stuff/, $(STUFF)) $(OUT)/aux
