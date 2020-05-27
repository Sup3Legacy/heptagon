
all:
	gcc *.c -Wall -pthread -l OpenCL -lm -o test_bin

# OLD Line for Parkas machine (for compilation on a NVIDIA GPU):
#	gcc *.c -pthread -I /usr/local/cuda/include -l OpenCL -o test_bin

clean:
	rm test_bin
