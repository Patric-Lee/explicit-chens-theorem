import PlattPointPacketKernel
import PlattPointPackets.L0B0064
import PlattPointPackets.L0B0065
import PlattPointPackets.L0B0066
import PlattPointPackets.L0B0067
import PlattPointPackets.L0B0068
import PlattPointPackets.L0B0069
import PlattPointPackets.L0B0070
import PlattPointPackets.L0B0071
import PlattPointPackets.L0B0072
import PlattPointPackets.L0B0073
import PlattPointPackets.L0B0074
import PlattPointPackets.L0B0075
import PlattPointPackets.L0B0076
import PlattPointPackets.L0B0077
import PlattPointPackets.L0B0078
import PlattPointPackets.L0B0079
import PlattPointPackets.L0B0080
import PlattPointPackets.L0B0081
import PlattPointPackets.L0B0082
import PlattPointPackets.L0B0083
import PlattPointPackets.L0B0084
import PlattPointPackets.L0B0085
namespace ChenEffective.PlattWindow.PointPackets.L1B0002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.L0B0064.points ++ ChenEffective.PlattWindow.PointPackets.L0B0065.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0066.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0067.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0068.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0069.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0070.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0071.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0072.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0073.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0074.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0075.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0076.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0077.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0078.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0079.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0080.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0081.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0082.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0083.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0084.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0085.points)
theorem certified : PointChainCertificate 7174094848 112773638050141 112774025806792 10000000000 116863011702975 116863401833309 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.L0B0064.certified) ChenEffective.PlattWindow.PointPackets.L0B0065.certified) ChenEffective.PlattWindow.PointPackets.L0B0066.certified) ChenEffective.PlattWindow.PointPackets.L0B0067.certified) ChenEffective.PlattWindow.PointPackets.L0B0068.certified) ChenEffective.PlattWindow.PointPackets.L0B0069.certified) ChenEffective.PlattWindow.PointPackets.L0B0070.certified) ChenEffective.PlattWindow.PointPackets.L0B0071.certified) ChenEffective.PlattWindow.PointPackets.L0B0072.certified) ChenEffective.PlattWindow.PointPackets.L0B0073.certified) ChenEffective.PlattWindow.PointPackets.L0B0074.certified) ChenEffective.PlattWindow.PointPackets.L0B0075.certified) ChenEffective.PlattWindow.PointPackets.L0B0076.certified) ChenEffective.PlattWindow.PointPackets.L0B0077.certified) ChenEffective.PlattWindow.PointPackets.L0B0078.certified) ChenEffective.PlattWindow.PointPackets.L0B0079.certified) ChenEffective.PlattWindow.PointPackets.L0B0080.certified) ChenEffective.PlattWindow.PointPackets.L0B0081.certified) ChenEffective.PlattWindow.PointPackets.L0B0082.certified) ChenEffective.PlattWindow.PointPackets.L0B0083.certified) ChenEffective.PlattWindow.PointPackets.L0B0084.certified) ChenEffective.PlattWindow.PointPackets.L0B0085.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L1B0002
