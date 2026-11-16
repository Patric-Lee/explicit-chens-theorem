import PlattPointPacketKernel
import PlattPointPackets.S6B000051
import PlattPointPackets.S6B000052
import PlattPointPackets.S6B000053
import PlattPointPackets.S6B000054
import PlattPointPackets.S6B000055
import PlattPointPackets.S6B000056
import PlattPointPackets.S6B000057
import PlattPointPackets.S6B000058
import PlattPointPackets.S6B000059
import PlattPointPackets.S6B000060
import PlattPointPackets.S6B000061
import PlattPointPackets.S6B000062
import PlattPointPackets.S6B000063
import PlattPointPackets.S6B000064
import PlattPointPackets.S6B000065
import PlattPointPackets.S6B000066
import PlattPointPackets.S6B000067
import PlattPointPackets.S6B000068
import PlattPointPackets.S6B000069
import PlattPointPackets.S6B000070
import PlattPointPackets.S6B000071
import PlattPointPackets.S6B000072
import PlattPointPackets.S6B000073
import PlattPointPackets.S6B000074
import PlattPointPackets.S6B000075
import PlattPointPackets.S6B000076
import PlattPointPackets.S6B000077
import PlattPointPackets.S6B000078
import PlattPointPackets.S6B000079
import PlattPointPackets.S6B000080
import PlattPointPackets.S6B000081
import PlattPointPackets.S6B000082
namespace ChenEffective.PlattWindow.PointPackets.L0B0061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000051.points ++ ChenEffective.PlattWindow.PointPackets.S6B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000064.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000071.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000082.points)
theorem certified : PointChainCertificate 6771441664 112056317790515 112056705139731 6905659392 112300249760691 112300637248566 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S6B000051.certified) ChenEffective.PlattWindow.PointPackets.S6B000052.certified) ChenEffective.PlattWindow.PointPackets.S6B000053.certified) ChenEffective.PlattWindow.PointPackets.S6B000054.certified) ChenEffective.PlattWindow.PointPackets.S6B000055.certified) ChenEffective.PlattWindow.PointPackets.S6B000056.certified) ChenEffective.PlattWindow.PointPackets.S6B000057.certified) ChenEffective.PlattWindow.PointPackets.S6B000058.certified) ChenEffective.PlattWindow.PointPackets.S6B000059.certified) ChenEffective.PlattWindow.PointPackets.S6B000060.certified) ChenEffective.PlattWindow.PointPackets.S6B000061.certified) ChenEffective.PlattWindow.PointPackets.S6B000062.certified) ChenEffective.PlattWindow.PointPackets.S6B000063.certified) ChenEffective.PlattWindow.PointPackets.S6B000064.certified) ChenEffective.PlattWindow.PointPackets.S6B000065.certified) ChenEffective.PlattWindow.PointPackets.S6B000066.certified) ChenEffective.PlattWindow.PointPackets.S6B000067.certified) ChenEffective.PlattWindow.PointPackets.S6B000068.certified) ChenEffective.PlattWindow.PointPackets.S6B000069.certified) ChenEffective.PlattWindow.PointPackets.S6B000070.certified) ChenEffective.PlattWindow.PointPackets.S6B000071.certified) ChenEffective.PlattWindow.PointPackets.S6B000072.certified) ChenEffective.PlattWindow.PointPackets.S6B000073.certified) ChenEffective.PlattWindow.PointPackets.S6B000074.certified) ChenEffective.PlattWindow.PointPackets.S6B000075.certified) ChenEffective.PlattWindow.PointPackets.S6B000076.certified) ChenEffective.PlattWindow.PointPackets.S6B000077.certified) ChenEffective.PlattWindow.PointPackets.S6B000078.certified) ChenEffective.PlattWindow.PointPackets.S6B000079.certified) ChenEffective.PlattWindow.PointPackets.S6B000080.certified) ChenEffective.PlattWindow.PointPackets.S6B000081.certified) ChenEffective.PlattWindow.PointPackets.S6B000082.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0061
