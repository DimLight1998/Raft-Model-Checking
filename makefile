SHELL=/bin/zsh

run: play.smv
	/bin/time -f "%MKB, %e real, %U user, %S system" nusmv -r play.smv \
		| colout true green | colout false red

int: play.smv
	nusmv -int play.smv

play.smv: play.template.smv makefile
	./gpp play.template.smv play.smv -DnumNode=5

clean:
	rm play.smv

