import PlattPointPacketKernel
import PlattPointPackets.S7B000090
import PlattPointPackets.S7B000091
import PlattPointPackets.S7B000092
import PlattPointPackets.S7B000093
import PlattPointPackets.S7B000094
import PlattPointPackets.S7B000095
import PlattPointPackets.S7B000096
import PlattPointPackets.S7B000097
import PlattPointPackets.S7B000098
import PlattPointPackets.S7B000099
import PlattPointPackets.S7B000100
import PlattPointPackets.S7B000101
import PlattPointPackets.S7B000102
import PlattPointPackets.S7B000103
import PlattPointPackets.S7B000104
import PlattPointPackets.S7B000105
import PlattPointPackets.S7B000106
import PlattPointPackets.S7B000107
import PlattPointPackets.S7B000108
import PlattPointPackets.S7B000109
import PlattPointPackets.S7B000110
import PlattPointPackets.S7B000111
import PlattPointPackets.S7B000112
import PlattPointPackets.S7B000113
import PlattPointPackets.S7B000114
import PlattPointPackets.S7B000115
import PlattPointPackets.S7B000116
import PlattPointPackets.S7B000117
import PlattPointPackets.S7B000118
import PlattPointPackets.S7B000119
import PlattPointPackets.S7B000120
import PlattPointPackets.S7B000121
namespace ChenEffective.PlattWindow.PointPackets.L0B0072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000090.points ++ ChenEffective.PlattWindow.PointPackets.S7B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000093.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000100.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000121.points)
theorem certified : PointChainCertificate 8245739520 114495130841481 114495519580149 8379957248 114694116420661 114694505273845 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000090.certified) ChenEffective.PlattWindow.PointPackets.S7B000091.certified) ChenEffective.PlattWindow.PointPackets.S7B000092.certified) ChenEffective.PlattWindow.PointPackets.S7B000093.certified) ChenEffective.PlattWindow.PointPackets.S7B000094.certified) ChenEffective.PlattWindow.PointPackets.S7B000095.certified) ChenEffective.PlattWindow.PointPackets.S7B000096.certified) ChenEffective.PlattWindow.PointPackets.S7B000097.certified) ChenEffective.PlattWindow.PointPackets.S7B000098.certified) ChenEffective.PlattWindow.PointPackets.S7B000099.certified) ChenEffective.PlattWindow.PointPackets.S7B000100.certified) ChenEffective.PlattWindow.PointPackets.S7B000101.certified) ChenEffective.PlattWindow.PointPackets.S7B000102.certified) ChenEffective.PlattWindow.PointPackets.S7B000103.certified) ChenEffective.PlattWindow.PointPackets.S7B000104.certified) ChenEffective.PlattWindow.PointPackets.S7B000105.certified) ChenEffective.PlattWindow.PointPackets.S7B000106.certified) ChenEffective.PlattWindow.PointPackets.S7B000107.certified) ChenEffective.PlattWindow.PointPackets.S7B000108.certified) ChenEffective.PlattWindow.PointPackets.S7B000109.certified) ChenEffective.PlattWindow.PointPackets.S7B000110.certified) ChenEffective.PlattWindow.PointPackets.S7B000111.certified) ChenEffective.PlattWindow.PointPackets.S7B000112.certified) ChenEffective.PlattWindow.PointPackets.S7B000113.certified) ChenEffective.PlattWindow.PointPackets.S7B000114.certified) ChenEffective.PlattWindow.PointPackets.S7B000115.certified) ChenEffective.PlattWindow.PointPackets.S7B000116.certified) ChenEffective.PlattWindow.PointPackets.S7B000117.certified) ChenEffective.PlattWindow.PointPackets.S7B000118.certified) ChenEffective.PlattWindow.PointPackets.S7B000119.certified) ChenEffective.PlattWindow.PointPackets.S7B000120.certified) ChenEffective.PlattWindow.PointPackets.S7B000121.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0072
