SRCS	= ool.c parse.c

all:
	clang -O3 -fomit-frame-pointer $(SRCS)

debug:
	clang -g $(SRCS)

clean:
	rm *~ a.out

