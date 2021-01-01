SHELL=/bin/zsh

run: play.smv
	nusmv play.smv \
		| colout true green | colout false red

int: play.smv
	nusmv -int play.smv

play.smv: play.template.smv
	./gpp play.template.smv play.smv -DnumNode=3

clean:
	rm play.smv

