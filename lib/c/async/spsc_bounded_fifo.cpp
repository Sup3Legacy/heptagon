
#include <atomic>
#include <iostream>

#ifndef CACHE_LINE_SIZE
#define CACHE_LINE_SIZE 64
#endif


using namespace std;

template<typename T>
typedef struct alignas(CACHE_LINE_SIZE) padded_data {
	T data;
} padded_data;

template<typename T, int size>
class Queue {
	T data_array[size];
	
	int alignas(CACHE_LINE_SIZE) prod_current;
	int alignas(CACHE_LINE_SIZE) conso_current;
	
	int prod_max, conso_max;

	void push

