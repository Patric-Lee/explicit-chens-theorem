import PlattPointPacketKernel
import PlattPointPackets.S8B000033
import PlattPointPackets.S8B000034
import PlattPointPackets.S8B000035
import PlattPointPackets.S8B000036
import PlattPointPackets.S8B000037
import PlattPointPackets.S8B000038
import PlattPointPackets.S8B000039
import PlattPointPackets.S8B000040
import PlattPointPackets.S8B000041
import PlattPointPackets.S8B000042
import PlattPointPackets.S8B000043
import PlattPointPackets.S8B000044
import PlattPointPackets.S8B000045
import PlattPointPackets.S8B000046
import PlattPointPackets.S8B000047
import PlattPointPackets.S8B000048
import PlattPointPackets.S8B000049
import PlattPointPackets.S8B000050
import PlattPointPackets.S8B000051
import PlattPointPackets.S8B000052
import PlattPointPackets.S8B000053
import PlattPointPackets.S8B000054
import PlattPointPackets.S8B000055
import PlattPointPackets.S8B000056
import PlattPointPackets.S8B000057
import PlattPointPackets.S8B000058
import PlattPointPackets.S8B000059
import PlattPointPackets.S8B000060
import PlattPointPackets.S8B000061
import PlattPointPackets.S8B000062
import PlattPointPackets.S8B000063
import PlattPointPackets.S8B000064
namespace ChenEffective.PlattWindow.PointPackets.L0B0080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000033.points ++ ChenEffective.PlattWindow.PointPackets.S8B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000064.points)
theorem certified : PointChainCertificate 9317384192 115997356638553 115997746252006 9451601920 116172665555902 116173055273189 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S8B000033.certified) ChenEffective.PlattWindow.PointPackets.S8B000034.certified) ChenEffective.PlattWindow.PointPackets.S8B000035.certified) ChenEffective.PlattWindow.PointPackets.S8B000036.certified) ChenEffective.PlattWindow.PointPackets.S8B000037.certified) ChenEffective.PlattWindow.PointPackets.S8B000038.certified) ChenEffective.PlattWindow.PointPackets.S8B000039.certified) ChenEffective.PlattWindow.PointPackets.S8B000040.certified) ChenEffective.PlattWindow.PointPackets.S8B000041.certified) ChenEffective.PlattWindow.PointPackets.S8B000042.certified) ChenEffective.PlattWindow.PointPackets.S8B000043.certified) ChenEffective.PlattWindow.PointPackets.S8B000044.certified) ChenEffective.PlattWindow.PointPackets.S8B000045.certified) ChenEffective.PlattWindow.PointPackets.S8B000046.certified) ChenEffective.PlattWindow.PointPackets.S8B000047.certified) ChenEffective.PlattWindow.PointPackets.S8B000048.certified) ChenEffective.PlattWindow.PointPackets.S8B000049.certified) ChenEffective.PlattWindow.PointPackets.S8B000050.certified) ChenEffective.PlattWindow.PointPackets.S8B000051.certified) ChenEffective.PlattWindow.PointPackets.S8B000052.certified) ChenEffective.PlattWindow.PointPackets.S8B000053.certified) ChenEffective.PlattWindow.PointPackets.S8B000054.certified) ChenEffective.PlattWindow.PointPackets.S8B000055.certified) ChenEffective.PlattWindow.PointPackets.S8B000056.certified) ChenEffective.PlattWindow.PointPackets.S8B000057.certified) ChenEffective.PlattWindow.PointPackets.S8B000058.certified) ChenEffective.PlattWindow.PointPackets.S8B000059.certified) ChenEffective.PlattWindow.PointPackets.S8B000060.certified) ChenEffective.PlattWindow.PointPackets.S8B000061.certified) ChenEffective.PlattWindow.PointPackets.S8B000062.certified) ChenEffective.PlattWindow.PointPackets.S8B000063.certified) ChenEffective.PlattWindow.PointPackets.S8B000064.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0080
