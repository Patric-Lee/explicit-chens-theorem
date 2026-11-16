import PlattPointPacketKernel
import PlattPointPackets.S5B000044
import PlattPointPackets.S5B000045
import PlattPointPackets.S5B000046
import PlattPointPackets.S5B000047
import PlattPointPackets.S5B000048
import PlattPointPackets.S5B000049
import PlattPointPackets.S5B000050
import PlattPointPackets.S5B000051
import PlattPointPackets.S5B000052
import PlattPointPackets.S5B000053
import PlattPointPackets.S5B000054
import PlattPointPackets.S5B000055
import PlattPointPackets.S5B000056
import PlattPointPackets.S5B000057
import PlattPointPackets.S5B000058
import PlattPointPackets.S5B000059
import PlattPointPackets.S5B000060
import PlattPointPackets.S5B000061
import PlattPointPackets.S5B000062
import PlattPointPackets.S5B000063
import PlattPointPackets.S5B000064
import PlattPointPackets.S5B000065
import PlattPointPackets.S5B000066
import PlattPointPackets.S5B000067
import PlattPointPackets.S5B000068
import PlattPointPackets.S5B000069
import PlattPointPackets.S5B000070
import PlattPointPackets.S5B000071
import PlattPointPackets.S5B000072
import PlattPointPackets.S5B000073
import PlattPointPackets.S5B000074
import PlattPointPackets.S5B000075
namespace ChenEffective.PlattWindow.PointPackets.L0B0051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000044.points ++ ChenEffective.PlattWindow.PointPackets.S5B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000064.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000071.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000075.points)
theorem certified : PointChainCertificate 5431361536 109300610935765 109300996698290 5565579264 109606991956824 109607377899032 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S5B000044.certified) ChenEffective.PlattWindow.PointPackets.S5B000045.certified) ChenEffective.PlattWindow.PointPackets.S5B000046.certified) ChenEffective.PlattWindow.PointPackets.S5B000047.certified) ChenEffective.PlattWindow.PointPackets.S5B000048.certified) ChenEffective.PlattWindow.PointPackets.S5B000049.certified) ChenEffective.PlattWindow.PointPackets.S5B000050.certified) ChenEffective.PlattWindow.PointPackets.S5B000051.certified) ChenEffective.PlattWindow.PointPackets.S5B000052.certified) ChenEffective.PlattWindow.PointPackets.S5B000053.certified) ChenEffective.PlattWindow.PointPackets.S5B000054.certified) ChenEffective.PlattWindow.PointPackets.S5B000055.certified) ChenEffective.PlattWindow.PointPackets.S5B000056.certified) ChenEffective.PlattWindow.PointPackets.S5B000057.certified) ChenEffective.PlattWindow.PointPackets.S5B000058.certified) ChenEffective.PlattWindow.PointPackets.S5B000059.certified) ChenEffective.PlattWindow.PointPackets.S5B000060.certified) ChenEffective.PlattWindow.PointPackets.S5B000061.certified) ChenEffective.PlattWindow.PointPackets.S5B000062.certified) ChenEffective.PlattWindow.PointPackets.S5B000063.certified) ChenEffective.PlattWindow.PointPackets.S5B000064.certified) ChenEffective.PlattWindow.PointPackets.S5B000065.certified) ChenEffective.PlattWindow.PointPackets.S5B000066.certified) ChenEffective.PlattWindow.PointPackets.S5B000067.certified) ChenEffective.PlattWindow.PointPackets.S5B000068.certified) ChenEffective.PlattWindow.PointPackets.S5B000069.certified) ChenEffective.PlattWindow.PointPackets.S5B000070.certified) ChenEffective.PlattWindow.PointPackets.S5B000071.certified) ChenEffective.PlattWindow.PointPackets.S5B000072.certified) ChenEffective.PlattWindow.PointPackets.S5B000073.certified) ChenEffective.PlattWindow.PointPackets.S5B000074.certified) ChenEffective.PlattWindow.PointPackets.S5B000075.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0051
