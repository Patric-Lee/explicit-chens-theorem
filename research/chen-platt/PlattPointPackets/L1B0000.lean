import PlattPointPacketKernel
import PlattPointPackets.L0B0000
import PlattPointPackets.L0B0001
import PlattPointPackets.L0B0002
import PlattPointPackets.L0B0003
import PlattPointPackets.L0B0004
import PlattPointPackets.L0B0005
import PlattPointPackets.L0B0006
import PlattPointPackets.L0B0007
import PlattPointPackets.L0B0008
import PlattPointPackets.L0B0009
import PlattPointPackets.L0B0010
import PlattPointPackets.L0B0011
import PlattPointPackets.L0B0012
import PlattPointPackets.L0B0013
import PlattPointPackets.L0B0014
import PlattPointPackets.L0B0015
import PlattPointPackets.L0B0016
import PlattPointPackets.L0B0017
import PlattPointPackets.L0B0018
import PlattPointPackets.L0B0019
import PlattPointPackets.L0B0020
import PlattPointPackets.L0B0021
import PlattPointPackets.L0B0022
import PlattPointPackets.L0B0023
import PlattPointPackets.L0B0024
import PlattPointPackets.L0B0025
import PlattPointPackets.L0B0026
import PlattPointPackets.L0B0027
import PlattPointPackets.L0B0028
import PlattPointPackets.L0B0029
import PlattPointPackets.L0B0030
import PlattPointPackets.L0B0031
namespace ChenEffective.PlattWindow.PointPackets.L1B0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.L0B0000.points ++ ChenEffective.PlattWindow.PointPackets.L0B0001.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0002.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0003.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0004.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0005.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0006.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0007.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0008.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0009.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0010.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0011.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0012.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0013.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0014.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0015.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0016.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0017.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0018.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0019.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0020.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0021.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0022.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0023.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0024.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0025.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0026.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0027.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0028.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0029.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0030.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0031.points)
theorem certified : PointChainCertificate 4000000 0 0 2885419008 101243892916966 101244273995877 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.L0B0000.certified) ChenEffective.PlattWindow.PointPackets.L0B0001.certified) ChenEffective.PlattWindow.PointPackets.L0B0002.certified) ChenEffective.PlattWindow.PointPackets.L0B0003.certified) ChenEffective.PlattWindow.PointPackets.L0B0004.certified) ChenEffective.PlattWindow.PointPackets.L0B0005.certified) ChenEffective.PlattWindow.PointPackets.L0B0006.certified) ChenEffective.PlattWindow.PointPackets.L0B0007.certified) ChenEffective.PlattWindow.PointPackets.L0B0008.certified) ChenEffective.PlattWindow.PointPackets.L0B0009.certified) ChenEffective.PlattWindow.PointPackets.L0B0010.certified) ChenEffective.PlattWindow.PointPackets.L0B0011.certified) ChenEffective.PlattWindow.PointPackets.L0B0012.certified) ChenEffective.PlattWindow.PointPackets.L0B0013.certified) ChenEffective.PlattWindow.PointPackets.L0B0014.certified) ChenEffective.PlattWindow.PointPackets.L0B0015.certified) ChenEffective.PlattWindow.PointPackets.L0B0016.certified) ChenEffective.PlattWindow.PointPackets.L0B0017.certified) ChenEffective.PlattWindow.PointPackets.L0B0018.certified) ChenEffective.PlattWindow.PointPackets.L0B0019.certified) ChenEffective.PlattWindow.PointPackets.L0B0020.certified) ChenEffective.PlattWindow.PointPackets.L0B0021.certified) ChenEffective.PlattWindow.PointPackets.L0B0022.certified) ChenEffective.PlattWindow.PointPackets.L0B0023.certified) ChenEffective.PlattWindow.PointPackets.L0B0024.certified) ChenEffective.PlattWindow.PointPackets.L0B0025.certified) ChenEffective.PlattWindow.PointPackets.L0B0026.certified) ChenEffective.PlattWindow.PointPackets.L0B0027.certified) ChenEffective.PlattWindow.PointPackets.L0B0028.certified) ChenEffective.PlattWindow.PointPackets.L0B0029.certified) ChenEffective.PlattWindow.PointPackets.L0B0030.certified) ChenEffective.PlattWindow.PointPackets.L0B0031.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L1B0000
