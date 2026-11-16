import PlattPointPacketKernel
import PlattPointPackets.S7B000026
import PlattPointPackets.S7B000027
import PlattPointPackets.S7B000028
import PlattPointPackets.S7B000029
import PlattPointPackets.S7B000030
import PlattPointPackets.S7B000031
import PlattPointPackets.S7B000032
import PlattPointPackets.S7B000033
import PlattPointPackets.S7B000034
import PlattPointPackets.S7B000035
import PlattPointPackets.S7B000036
import PlattPointPackets.S7B000037
import PlattPointPackets.S7B000038
import PlattPointPackets.S7B000039
import PlattPointPackets.S7B000040
import PlattPointPackets.S7B000041
import PlattPointPackets.S7B000042
import PlattPointPackets.S7B000043
import PlattPointPackets.S7B000044
import PlattPointPackets.S7B000045
import PlattPointPackets.S7B000046
import PlattPointPackets.S7B000047
import PlattPointPackets.S7B000048
import PlattPointPackets.S7B000049
import PlattPointPackets.S7B000050
import PlattPointPackets.S7B000051
import PlattPointPackets.S7B000052
import PlattPointPackets.S7B000053
import PlattPointPackets.S7B000054
import PlattPointPackets.S7B000055
import PlattPointPackets.S7B000056
import PlattPointPackets.S7B000057
namespace ChenEffective.PlattWindow.PointPackets.L0B0070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000026.points ++ ChenEffective.PlattWindow.PointPackets.S7B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000057.points)
theorem certified : PointChainCertificate 7977304064 114086779467393 114087167971777 8111521792 114292730171484 114293118793804 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000026.certified) ChenEffective.PlattWindow.PointPackets.S7B000027.certified) ChenEffective.PlattWindow.PointPackets.S7B000028.certified) ChenEffective.PlattWindow.PointPackets.S7B000029.certified) ChenEffective.PlattWindow.PointPackets.S7B000030.certified) ChenEffective.PlattWindow.PointPackets.S7B000031.certified) ChenEffective.PlattWindow.PointPackets.S7B000032.certified) ChenEffective.PlattWindow.PointPackets.S7B000033.certified) ChenEffective.PlattWindow.PointPackets.S7B000034.certified) ChenEffective.PlattWindow.PointPackets.S7B000035.certified) ChenEffective.PlattWindow.PointPackets.S7B000036.certified) ChenEffective.PlattWindow.PointPackets.S7B000037.certified) ChenEffective.PlattWindow.PointPackets.S7B000038.certified) ChenEffective.PlattWindow.PointPackets.S7B000039.certified) ChenEffective.PlattWindow.PointPackets.S7B000040.certified) ChenEffective.PlattWindow.PointPackets.S7B000041.certified) ChenEffective.PlattWindow.PointPackets.S7B000042.certified) ChenEffective.PlattWindow.PointPackets.S7B000043.certified) ChenEffective.PlattWindow.PointPackets.S7B000044.certified) ChenEffective.PlattWindow.PointPackets.S7B000045.certified) ChenEffective.PlattWindow.PointPackets.S7B000046.certified) ChenEffective.PlattWindow.PointPackets.S7B000047.certified) ChenEffective.PlattWindow.PointPackets.S7B000048.certified) ChenEffective.PlattWindow.PointPackets.S7B000049.certified) ChenEffective.PlattWindow.PointPackets.S7B000050.certified) ChenEffective.PlattWindow.PointPackets.S7B000051.certified) ChenEffective.PlattWindow.PointPackets.S7B000052.certified) ChenEffective.PlattWindow.PointPackets.S7B000053.certified) ChenEffective.PlattWindow.PointPackets.S7B000054.certified) ChenEffective.PlattWindow.PointPackets.S7B000055.certified) ChenEffective.PlattWindow.PointPackets.S7B000056.certified) ChenEffective.PlattWindow.PointPackets.S7B000057.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0070
