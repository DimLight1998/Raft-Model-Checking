SHELL=/bin/zsh

run: raft.generated.smv
	/bin/time -f "%MKB, %e real, %U user, %S system" nusmv -r raft.generated.smv | grep -v "^\*\*\*" \
		| colout true green | colout false red

int: raft.generated.smv
	nusmv -int raft.generated.smv

raft.generated.smv: raft.template.smv makefile
	./gpp raft.template.smv raft.generated.smv -DnumNode=3

clean:
	rm raft.generated.smv

