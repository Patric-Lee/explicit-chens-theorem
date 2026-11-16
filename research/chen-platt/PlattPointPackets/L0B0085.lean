import PlattPointPacketKernel
import PlattPointPackets.S8B000193
import PlattPointPackets.S8B000194
import PlattPointPackets.S8B000195
namespace ChenEffective.PlattWindow.PointPackets.L0B0085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S8B000193.points ++ ChenEffective.PlattWindow.PointPackets.S8B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000195.points)
theorem certified : PointChainCertificate 9988472832 116848910688344 116849300810138 10000000000 116863011702975 116863401833309 points := PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S8B000193.certified) ChenEffective.PlattWindow.PointPackets.S8B000194.certified) ChenEffective.PlattWindow.PointPackets.S8B000195.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0085
