import PlattPointPacketKernel
import PlattPointPackets.S8B000001
import PlattPointPackets.S8B000002
import PlattPointPackets.S8B000003
import PlattPointPackets.S8B000004
import PlattPointPackets.S8B000005
import PlattPointPackets.S8B000006
import PlattPointPackets.S8B000007
import PlattPointPackets.S8B000008
import PlattPointPackets.S8B000009
import PlattPointPackets.S8B000010
import PlattPointPackets.S8B000011
import PlattPointPackets.S8B000012
import PlattPointPackets.S8B000013
import PlattPointPackets.S8B000014
import PlattPointPackets.S8B000015
import PlattPointPackets.S8B000016
import PlattPointPackets.S8B000017
import PlattPointPackets.S8B000018
import PlattPointPackets.S8B000019
import PlattPointPackets.S8B000020
import PlattPointPackets.S8B000021
import PlattPointPackets.S8B000022
import PlattPointPackets.S8B000023
import PlattPointPackets.S8B000024
import PlattPointPackets.S8B000025
import PlattPointPackets.S8B000026
import PlattPointPackets.S8B000027
import PlattPointPackets.S8B000028
import PlattPointPackets.S8B000029
import PlattPointPackets.S8B000030
import PlattPointPackets.S8B000031
import PlattPointPackets.S8B000032
namespace ChenEffective.PlattWindow.PointPackets.L0B0079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000001.points ++ ChenEffective.PlattWindow.PointPackets.S8B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000032.points)
theorem certified : PointChainCertificate 9183166464 115819334242089 115819723750598 9317384192 115997356638553 115997746252006 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S8B000001.certified) ChenEffective.PlattWindow.PointPackets.S8B000002.certified) ChenEffective.PlattWindow.PointPackets.S8B000003.certified) ChenEffective.PlattWindow.PointPackets.S8B000004.certified) ChenEffective.PlattWindow.PointPackets.S8B000005.certified) ChenEffective.PlattWindow.PointPackets.S8B000006.certified) ChenEffective.PlattWindow.PointPackets.S8B000007.certified) ChenEffective.PlattWindow.PointPackets.S8B000008.certified) ChenEffective.PlattWindow.PointPackets.S8B000009.certified) ChenEffective.PlattWindow.PointPackets.S8B000010.certified) ChenEffective.PlattWindow.PointPackets.S8B000011.certified) ChenEffective.PlattWindow.PointPackets.S8B000012.certified) ChenEffective.PlattWindow.PointPackets.S8B000013.certified) ChenEffective.PlattWindow.PointPackets.S8B000014.certified) ChenEffective.PlattWindow.PointPackets.S8B000015.certified) ChenEffective.PlattWindow.PointPackets.S8B000016.certified) ChenEffective.PlattWindow.PointPackets.S8B000017.certified) ChenEffective.PlattWindow.PointPackets.S8B000018.certified) ChenEffective.PlattWindow.PointPackets.S8B000019.certified) ChenEffective.PlattWindow.PointPackets.S8B000020.certified) ChenEffective.PlattWindow.PointPackets.S8B000021.certified) ChenEffective.PlattWindow.PointPackets.S8B000022.certified) ChenEffective.PlattWindow.PointPackets.S8B000023.certified) ChenEffective.PlattWindow.PointPackets.S8B000024.certified) ChenEffective.PlattWindow.PointPackets.S8B000025.certified) ChenEffective.PlattWindow.PointPackets.S8B000026.certified) ChenEffective.PlattWindow.PointPackets.S8B000027.certified) ChenEffective.PlattWindow.PointPackets.S8B000028.certified) ChenEffective.PlattWindow.PointPackets.S8B000029.certified) ChenEffective.PlattWindow.PointPackets.S8B000030.certified) ChenEffective.PlattWindow.PointPackets.S8B000031.certified) ChenEffective.PlattWindow.PointPackets.S8B000032.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0079
