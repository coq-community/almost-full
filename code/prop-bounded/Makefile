COQC = "coqc"
COQFILES = ${shell ls *v}

all :
	$(COQC) AlmostFull.v
	$(COQC) AFConstructions.v
	$(COQC) AlmostFullInduction.v
	$(COQC) AFExamples.v
	$(COQC) Terminator.v
	$(COQC) AlmostFullGeneralized.v

clean : 
	rm ./*vo
	rm ./*glob
	rm ./*~ 

.DEFAULT : all

