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
        private static extern unsafe void*
            mmap(void* addr, uint length, int prot, int flags,
                int fd, int offset);

        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
        private delegate Int64 SomeFunc();

        private IntPtr p;
        private uint realSize;

        public Loader()
        {
            allocMem(stdSize);
            realSize = stdSize;
        }

        private const uint stdSize = 100000;

        private void allocMem(uint size)
        {
            IntPtr t;
            unsafe
            {
                var p = mmap(null, size, 4 | 1 | 2, 0x20 | 0x02, -1, 0);
                if ((Int64) p == -1)
                {
                    throw new Exception("allocate fail!"); 
                }
                t = new IntPtr(p);
            }

            p = t;
            realSize = size;
        }
        public void Load(Assembler asm) 
        {
            var codeStream = new MemoryStream();
            unsafe
            {
                var uIntPtr = new UIntPtr(p.ToPointer());
                asm.Assemble(new StreamCodeWriter(codeStream), uIntPtr.ToUInt64());
                if (codeStream.Length > realSize)
                {
                    allocMem((uint)codeStream.Length + 1024);
                    codeStream.Flush();
                    uIntPtr = new UIntPtr(p.ToPointer());
                    asm.Assemble(new StreamCodeWriter(codeStream), uIntPtr.ToUInt64());
                }
                byte* pchar = (byte*) p.ToPointer();
                BinaryReader r = new BinaryReader(codeStream);
                codeStream.Position = 0;
                while (codeStream.Position < codeStream.Length)
                {
                    *pchar = r.ReadByte();
                    pchar = pchar + 1;
                }
            }
        }

        public Int64 Exec()
        {
            var f = Marshal.GetDelegateForFunctionPointer<SomeFunc>(p);
            return f();
        }
    }
}