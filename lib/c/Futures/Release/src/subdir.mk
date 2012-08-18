################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CPP_SRCS += \
../src/_main.cpp \
../src/simple.cpp \
../src/simple_a.cpp 

OBJS += \
./src/_main.o \
./src/simple.o \
./src/simple_a.o 

CPP_DEPS += \
./src/_main.d \
./src/simple.d \
./src/simple_a.d 


# Each subdirectory must supply rules for building sources it contributes
src/%.o: ../src/%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: Cross G++ Compiler'
	/opt/local/bin/g++ -O3 -Wall -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@:%.o=%.d)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


