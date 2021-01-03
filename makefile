SHELL=/bin/zsh

run: raft.smv
	/bin/time -f "%MKB, %e real, %U user, %S system" nusmv -r raft.smv | grep -v "^\*\*\*" \
		| colout true green | colout false red

int: raft.smv
	nusmv -int raft.smv

raft.smv: raft.template.smv makefile
	./gpp raft.template.smv raft.smv -DnumNode=4

clean:
	rm raft.smv

