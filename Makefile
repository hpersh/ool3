CC	= clang
SRCS	= ool.c parse.c

all:
	$(CC) -O3 -fomit-frame-pointer $(SRCS)

debug:
	$(CC) -g $(SRCS)

clean:
	rm *~ a.out

