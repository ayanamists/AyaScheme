using System;
using System.Diagnostics;
using System.IO;
using Iced.Intel;
using System.IO.MemoryMappedFiles;
using System.Runtime.InteropServices;

namespace ACompilerLoader
{
    public class Loader
    {
        [DllImport("libc.so.6")]
        private static extern int getpid();
        [DllImport("libc.so.6")]
        private static extern unsafe void* 
            mmap(void* addr, uint length, int prot, int flags,
                 int fd, int offset);

        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
        private delegate Int64 SomeFunc();

        private Assembler asm;
        public Loader(Assembler asm)
        {
            this.asm = asm;
            
        }

        public UInt64 Load()
        {
            var codeStream = new MemoryStream();
            unsafe
            {
                void* p = mmap(null, 1024, 4 | 1 | 2, 0x20 | 0x02, -1, 0);
                if ((Int64) p == -1)
                {
                    throw new Exception("allocate fail!");
                }
                else
                {
                    var uIntPtr = new UIntPtr(p);
                    var ptr = new IntPtr(p);
                    byte* pchar = (byte*) p;
                    asm.Assemble(new StreamCodeWriter(codeStream), uIntPtr.ToUInt64());
                    BinaryReader r = new BinaryReader(codeStream);
                    byte[] arr = new byte[20];
                    codeStream.Position = 0;
                    while (codeStream.Position < codeStream.Length)
                    {
                        *pchar = r.ReadByte();
                        pchar = pchar + 1;
                    }
                    var f = Marshal.GetDelegateForFunctionPointer<SomeFunc>(ptr);
                    var res = f();
                    Console.WriteLine(res);
                    return 0;
                }
            }
        }
    }
}