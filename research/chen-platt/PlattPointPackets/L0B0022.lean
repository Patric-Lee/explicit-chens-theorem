import PlattPointPacketKernel
import PlattPointPackets.S2B000055
import PlattPointPackets.S2B000056
import PlattPointPackets.S2B000057
import PlattPointPackets.S2B000058
import PlattPointPackets.S2B000059
import PlattPointPackets.S2B000060
import PlattPointPackets.S2B000061
import PlattPointPackets.S2B000062
import PlattPointPackets.S2B000063
import PlattPointPackets.S2B000064
import PlattPointPackets.S2B000065
import PlattPointPackets.S2B000066
import PlattPointPackets.S2B000067
import PlattPointPackets.S2B000068
import PlattPointPackets.S2B000069
import PlattPointPackets.S2B000070
import PlattPointPackets.S2B000071
import PlattPointPackets.S2B000072
import PlattPointPackets.S2B000073
import PlattPointPackets.S2B000074
import PlattPointPackets.S2B000075
import PlattPointPackets.S2B000076
import PlattPointPackets.S2B000077
import PlattPointPackets.S2B000078
import PlattPointPackets.S2B000079
import PlattPointPackets.S2B000080
import PlattPointPackets.S2B000081
import PlattPointPackets.S2B000082
import PlattPointPackets.S2B000083
import PlattPointPackets.S2B000084
import PlattPointPackets.S2B000085
import PlattPointPackets.S2B000086
namespace ChenEffective.PlattWindow.PointPackets.L0B0022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S2B000055.points ++ ChenEffective.PlattWindow.PointPackets.S2B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000064.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000071.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000082.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000083.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000086.points)
theorem certified : PointChainCertificate 1545338880 93057374045556 93057749774939 1679556608 94163095056674 94163471620158 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S2B000055.certified) ChenEffective.PlattWindow.PointPackets.S2B000056.certified) ChenEffective.PlattWindow.PointPackets.S2B000057.certified) ChenEffective.PlattWindow.PointPackets.S2B000058.certified) ChenEffective.PlattWindow.PointPackets.S2B000059.certified) ChenEffective.PlattWindow.PointPackets.S2B000060.certified) ChenEffective.PlattWindow.PointPackets.S2B000061.certified) ChenEffective.PlattWindow.PointPackets.S2B000062.certified) ChenEffective.PlattWindow.PointPackets.S2B000063.certified) ChenEffective.PlattWindow.PointPackets.S2B000064.certified) ChenEffective.PlattWindow.PointPackets.S2B000065.certified) ChenEffective.PlattWindow.PointPackets.S2B000066.certified) ChenEffective.PlattWindow.PointPackets.S2B000067.certified) ChenEffective.PlattWindow.PointPackets.S2B000068.certified) ChenEffective.PlattWindow.PointPackets.S2B000069.certified) ChenEffective.PlattWindow.PointPackets.S2B000070.certified) ChenEffective.PlattWindow.PointPackets.S2B000071.certified) ChenEffective.PlattWindow.PointPackets.S2B000072.certified) ChenEffective.PlattWindow.PointPackets.S2B000073.certified) ChenEffective.PlattWindow.PointPackets.S2B000074.certified) ChenEffective.PlattWindow.PointPackets.S2B000075.certified) ChenEffective.PlattWindow.PointPackets.S2B000076.certified) ChenEffective.PlattWindow.PointPackets.S2B000077.certified) ChenEffective.PlattWindow.PointPackets.S2B000078.certified) ChenEffective.PlattWindow.PointPackets.S2B000079.certified) ChenEffective.PlattWindow.PointPackets.S2B000080.certified) ChenEffective.PlattWindow.PointPackets.S2B000081.certified) ChenEffective.PlattWindow.PointPackets.S2B000082.certified) ChenEffective.PlattWindow.PointPackets.S2B000083.certified) ChenEffective.PlattWindow.PointPackets.S2B000084.certified) ChenEffective.PlattWindow.PointPackets.S2B000085.certified) ChenEffective.PlattWindow.PointPackets.S2B000086.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0022
