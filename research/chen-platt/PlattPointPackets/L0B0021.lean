import PlattPointPacketKernel
import PlattPointPackets.S2B000023
import PlattPointPackets.S2B000024
import PlattPointPackets.S2B000025
import PlattPointPackets.S2B000026
import PlattPointPackets.S2B000027
import PlattPointPackets.S2B000028
import PlattPointPackets.S2B000029
import PlattPointPackets.S2B000030
import PlattPointPackets.S2B000031
import PlattPointPackets.S2B000032
import PlattPointPackets.S2B000033
import PlattPointPackets.S2B000034
import PlattPointPackets.S2B000035
import PlattPointPackets.S2B000036
import PlattPointPackets.S2B000037
import PlattPointPackets.S2B000038
import PlattPointPackets.S2B000039
import PlattPointPackets.S2B000040
import PlattPointPackets.S2B000041
import PlattPointPackets.S2B000042
import PlattPointPackets.S2B000043
import PlattPointPackets.S2B000044
import PlattPointPackets.S2B000045
import PlattPointPackets.S2B000046
import PlattPointPackets.S2B000047
import PlattPointPackets.S2B000048
import PlattPointPackets.S2B000049
import PlattPointPackets.S2B000050
import PlattPointPackets.S2B000051
import PlattPointPackets.S2B000052
import PlattPointPackets.S2B000053
import PlattPointPackets.S2B000054
namespace ChenEffective.PlattWindow.PointPackets.L0B0021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S2B000023.points ++ ChenEffective.PlattWindow.PointPackets.S2B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000054.points)
theorem certified : PointChainCertificate 1411121152 91845917373446 91846292131553 1545338880 93057374045556 93057749774939 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S2B000023.certified) ChenEffective.PlattWindow.PointPackets.S2B000024.certified) ChenEffective.PlattWindow.PointPackets.S2B000025.certified) ChenEffective.PlattWindow.PointPackets.S2B000026.certified) ChenEffective.PlattWindow.PointPackets.S2B000027.certified) ChenEffective.PlattWindow.PointPackets.S2B000028.certified) ChenEffective.PlattWindow.PointPackets.S2B000029.certified) ChenEffective.PlattWindow.PointPackets.S2B000030.certified) ChenEffective.PlattWindow.PointPackets.S2B000031.certified) ChenEffective.PlattWindow.PointPackets.S2B000032.certified) ChenEffective.PlattWindow.PointPackets.S2B000033.certified) ChenEffective.PlattWindow.PointPackets.S2B000034.certified) ChenEffective.PlattWindow.PointPackets.S2B000035.certified) ChenEffective.PlattWindow.PointPackets.S2B000036.certified) ChenEffective.PlattWindow.PointPackets.S2B000037.certified) ChenEffective.PlattWindow.PointPackets.S2B000038.certified) ChenEffective.PlattWindow.PointPackets.S2B000039.certified) ChenEffective.PlattWindow.PointPackets.S2B000040.certified) ChenEffective.PlattWindow.PointPackets.S2B000041.certified) ChenEffective.PlattWindow.PointPackets.S2B000042.certified) ChenEffective.PlattWindow.PointPackets.S2B000043.certified) ChenEffective.PlattWindow.PointPackets.S2B000044.certified) ChenEffective.PlattWindow.PointPackets.S2B000045.certified) ChenEffective.PlattWindow.PointPackets.S2B000046.certified) ChenEffective.PlattWindow.PointPackets.S2B000047.certified) ChenEffective.PlattWindow.PointPackets.S2B000048.certified) ChenEffective.PlattWindow.PointPackets.S2B000049.certified) ChenEffective.PlattWindow.PointPackets.S2B000050.certified) ChenEffective.PlattWindow.PointPackets.S2B000051.certified) ChenEffective.PlattWindow.PointPackets.S2B000052.certified) ChenEffective.PlattWindow.PointPackets.S2B000053.certified) ChenEffective.PlattWindow.PointPackets.S2B000054.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0021
