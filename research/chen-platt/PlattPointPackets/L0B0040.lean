import PlattPointPacketKernel
import PlattPointPackets.S4B000005
import PlattPointPackets.S4B000006
import PlattPointPackets.S4B000007
import PlattPointPackets.S4B000008
import PlattPointPackets.S4B000009
import PlattPointPackets.S4B000010
import PlattPointPackets.S4B000011
import PlattPointPackets.S4B000012
import PlattPointPackets.S4B000013
import PlattPointPackets.S4B000014
import PlattPointPackets.S4B000015
import PlattPointPackets.S4B000016
import PlattPointPackets.S4B000017
import PlattPointPackets.S4B000018
import PlattPointPackets.S4B000019
import PlattPointPackets.S4B000020
import PlattPointPackets.S4B000021
import PlattPointPackets.S4B000022
import PlattPointPackets.S4B000023
import PlattPointPackets.S4B000024
import PlattPointPackets.S4B000025
import PlattPointPackets.S4B000026
import PlattPointPackets.S4B000027
import PlattPointPackets.S4B000028
import PlattPointPackets.S4B000029
import PlattPointPackets.S4B000030
import PlattPointPackets.S4B000031
import PlattPointPackets.S4B000032
import PlattPointPackets.S4B000033
import PlattPointPackets.S4B000034
import PlattPointPackets.S4B000035
import PlattPointPackets.S4B000036
namespace ChenEffective.PlattWindow.PointPackets.L0B0040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S4B000005.points ++ ChenEffective.PlattWindow.PointPackets.S4B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000036.points)
theorem certified : PointChainCertificate 3957063680 105295690457495 105296073816827 4091281408 105720145108166 105720528706356 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S4B000005.certified) ChenEffective.PlattWindow.PointPackets.S4B000006.certified) ChenEffective.PlattWindow.PointPackets.S4B000007.certified) ChenEffective.PlattWindow.PointPackets.S4B000008.certified) ChenEffective.PlattWindow.PointPackets.S4B000009.certified) ChenEffective.PlattWindow.PointPackets.S4B000010.certified) ChenEffective.PlattWindow.PointPackets.S4B000011.certified) ChenEffective.PlattWindow.PointPackets.S4B000012.certified) ChenEffective.PlattWindow.PointPackets.S4B000013.certified) ChenEffective.PlattWindow.PointPackets.S4B000014.certified) ChenEffective.PlattWindow.PointPackets.S4B000015.certified) ChenEffective.PlattWindow.PointPackets.S4B000016.certified) ChenEffective.PlattWindow.PointPackets.S4B000017.certified) ChenEffective.PlattWindow.PointPackets.S4B000018.certified) ChenEffective.PlattWindow.PointPackets.S4B000019.certified) ChenEffective.PlattWindow.PointPackets.S4B000020.certified) ChenEffective.PlattWindow.PointPackets.S4B000021.certified) ChenEffective.PlattWindow.PointPackets.S4B000022.certified) ChenEffective.PlattWindow.PointPackets.S4B000023.certified) ChenEffective.PlattWindow.PointPackets.S4B000024.certified) ChenEffective.PlattWindow.PointPackets.S4B000025.certified) ChenEffective.PlattWindow.PointPackets.S4B000026.certified) ChenEffective.PlattWindow.PointPackets.S4B000027.certified) ChenEffective.PlattWindow.PointPackets.S4B000028.certified) ChenEffective.PlattWindow.PointPackets.S4B000029.certified) ChenEffective.PlattWindow.PointPackets.S4B000030.certified) ChenEffective.PlattWindow.PointPackets.S4B000031.certified) ChenEffective.PlattWindow.PointPackets.S4B000032.certified) ChenEffective.PlattWindow.PointPackets.S4B000033.certified) ChenEffective.PlattWindow.PointPackets.S4B000034.certified) ChenEffective.PlattWindow.PointPackets.S4B000035.certified) ChenEffective.PlattWindow.PointPackets.S4B000036.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0040
