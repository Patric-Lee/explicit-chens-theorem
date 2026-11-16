import PlattPointPacketKernel
import PlattPointPackets.S7B000058
import PlattPointPackets.S7B000059
import PlattPointPackets.S7B000060
import PlattPointPackets.S7B000061
import PlattPointPackets.S7B000062
import PlattPointPackets.S7B000063
import PlattPointPackets.S7B000064
import PlattPointPackets.S7B000065
import PlattPointPackets.S7B000066
import PlattPointPackets.S7B000067
import PlattPointPackets.S7B000068
import PlattPointPackets.S7B000069
import PlattPointPackets.S7B000070
import PlattPointPackets.S7B000071
import PlattPointPackets.S7B000072
import PlattPointPackets.S7B000073
import PlattPointPackets.S7B000074
import PlattPointPackets.S7B000075
import PlattPointPackets.S7B000076
import PlattPointPackets.S7B000077
import PlattPointPackets.S7B000078
import PlattPointPackets.S7B000079
import PlattPointPackets.S7B000080
import PlattPointPackets.S7B000081
import PlattPointPackets.S7B000082
import PlattPointPackets.S7B000083
import PlattPointPackets.S7B000084
import PlattPointPackets.S7B000085
import PlattPointPackets.S7B000086
import PlattPointPackets.S7B000087
import PlattPointPackets.S7B000088
import PlattPointPackets.S7B000089
namespace ChenEffective.PlattWindow.PointPackets.L0B0071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000058.points ++ ChenEffective.PlattWindow.PointPackets.S7B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000064.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000071.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000082.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000083.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000086.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000087.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000088.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000089.points)
theorem certified : PointChainCertificate 8111521792 114292730171484 114293118793804 8245739520 114495130841481 114495519580149 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000058.certified) ChenEffective.PlattWindow.PointPackets.S7B000059.certified) ChenEffective.PlattWindow.PointPackets.S7B000060.certified) ChenEffective.PlattWindow.PointPackets.S7B000061.certified) ChenEffective.PlattWindow.PointPackets.S7B000062.certified) ChenEffective.PlattWindow.PointPackets.S7B000063.certified) ChenEffective.PlattWindow.PointPackets.S7B000064.certified) ChenEffective.PlattWindow.PointPackets.S7B000065.certified) ChenEffective.PlattWindow.PointPackets.S7B000066.certified) ChenEffective.PlattWindow.PointPackets.S7B000067.certified) ChenEffective.PlattWindow.PointPackets.S7B000068.certified) ChenEffective.PlattWindow.PointPackets.S7B000069.certified) ChenEffective.PlattWindow.PointPackets.S7B000070.certified) ChenEffective.PlattWindow.PointPackets.S7B000071.certified) ChenEffective.PlattWindow.PointPackets.S7B000072.certified) ChenEffective.PlattWindow.PointPackets.S7B000073.certified) ChenEffective.PlattWindow.PointPackets.S7B000074.certified) ChenEffective.PlattWindow.PointPackets.S7B000075.certified) ChenEffective.PlattWindow.PointPackets.S7B000076.certified) ChenEffective.PlattWindow.PointPackets.S7B000077.certified) ChenEffective.PlattWindow.PointPackets.S7B000078.certified) ChenEffective.PlattWindow.PointPackets.S7B000079.certified) ChenEffective.PlattWindow.PointPackets.S7B000080.certified) ChenEffective.PlattWindow.PointPackets.S7B000081.certified) ChenEffective.PlattWindow.PointPackets.S7B000082.certified) ChenEffective.PlattWindow.PointPackets.S7B000083.certified) ChenEffective.PlattWindow.PointPackets.S7B000084.certified) ChenEffective.PlattWindow.PointPackets.S7B000085.certified) ChenEffective.PlattWindow.PointPackets.S7B000086.certified) ChenEffective.PlattWindow.PointPackets.S7B000087.certified) ChenEffective.PlattWindow.PointPackets.S7B000088.certified) ChenEffective.PlattWindow.PointPackets.S7B000089.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0071
