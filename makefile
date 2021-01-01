SHELL=/bin/zsh

run:
	./gpp play.template.smv play.smv -DnumNode=3
	nusmv play.smv

clean:
	rm play.smv

