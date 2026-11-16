import PlattPointPacketKernel
import PlattPointPackets.L1B0000
import PlattPointPackets.L1B0001
import PlattPointPackets.L1B0002
namespace ChenEffective.PlattWindow.PointPackets.L2B0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.L1B0000.points ++ ChenEffective.PlattWindow.PointPackets.L1B0001.points) ++ ChenEffective.PlattWindow.PointPackets.L1B0002.points)
theorem certified : PointChainCertificate 4000000 0 0 10000000000 116863011702975 116863401833309 points := PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.L1B0000.certified) ChenEffective.PlattWindow.PointPackets.L1B0001.certified) ChenEffective.PlattWindow.PointPackets.L1B0002.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L2B0000
