ASM_FILE=$1
nasm -fmacho64 $ASM_FILE.asm
ld -lSystem -L$(xcode-select -p)/SDKs/MacOSX.sdk/usr/lib $ASM_FILE.o -o $ASM_FILE
rm $ASM_FILE.o 2>/dev/null