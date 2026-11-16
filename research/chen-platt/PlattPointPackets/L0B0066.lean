import PlattPointPacketKernel
import PlattPointPackets.S6B000211
import PlattPointPackets.S6B000212
import PlattPointPackets.S6B000213
import PlattPointPackets.S6B000214
import PlattPointPackets.S6B000215
import PlattPointPackets.S6B000216
import PlattPointPackets.S6B000217
import PlattPointPackets.S6B000218
import PlattPointPackets.S6B000219
import PlattPointPackets.S6B000220
import PlattPointPackets.S6B000221
import PlattPointPackets.S6B000222
import PlattPointPackets.S6B000223
import PlattPointPackets.S6B000224
import PlattPointPackets.S6B000225
import PlattPointPackets.S6B000226
import PlattPointPackets.S6B000227
import PlattPointPackets.S6B000228
import PlattPointPackets.S6B000229
import PlattPointPackets.S6B000230
import PlattPointPackets.S6B000231
import PlattPointPackets.S6B000232
import PlattPointPackets.S6B000233
import PlattPointPackets.S6B000234
import PlattPointPackets.S6B000235
import PlattPointPackets.S6B000236
import PlattPointPackets.S6B000237
import PlattPointPackets.S6B000238
import PlattPointPackets.S6B000239
import PlattPointPackets.S6B000240
import PlattPointPackets.S6B000241
import PlattPointPackets.S6B000242
namespace ChenEffective.PlattWindow.PointPackets.L0B0066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000211.points ++ ChenEffective.PlattWindow.PointPackets.S6B000212.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000213.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000214.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000215.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000216.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000217.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000218.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000220.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000221.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000223.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000224.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000225.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000226.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000227.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000228.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000229.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000230.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000231.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000232.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000233.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000234.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000235.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000236.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000237.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000238.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000239.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000240.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000241.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000242.points)
theorem certified : PointChainCertificate 7442530304 113228879485900 113229267500985 7576748032 113450102524772 113450490665732 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S6B000211.certified) ChenEffective.PlattWindow.PointPackets.S6B000212.certified) ChenEffective.PlattWindow.PointPackets.S6B000213.certified) ChenEffective.PlattWindow.PointPackets.S6B000214.certified) ChenEffective.PlattWindow.PointPackets.S6B000215.certified) ChenEffective.PlattWindow.PointPackets.S6B000216.certified) ChenEffective.PlattWindow.PointPackets.S6B000217.certified) ChenEffective.PlattWindow.PointPackets.S6B000218.certified) ChenEffective.PlattWindow.PointPackets.S6B000219.certified) ChenEffective.PlattWindow.PointPackets.S6B000220.certified) ChenEffective.PlattWindow.PointPackets.S6B000221.certified) ChenEffective.PlattWindow.PointPackets.S6B000222.certified) ChenEffective.PlattWindow.PointPackets.S6B000223.certified) ChenEffective.PlattWindow.PointPackets.S6B000224.certified) ChenEffective.PlattWindow.PointPackets.S6B000225.certified) ChenEffective.PlattWindow.PointPackets.S6B000226.certified) ChenEffective.PlattWindow.PointPackets.S6B000227.certified) ChenEffective.PlattWindow.PointPackets.S6B000228.certified) ChenEffective.PlattWindow.PointPackets.S6B000229.certified) ChenEffective.PlattWindow.PointPackets.S6B000230.certified) ChenEffective.PlattWindow.PointPackets.S6B000231.certified) ChenEffective.PlattWindow.PointPackets.S6B000232.certified) ChenEffective.PlattWindow.PointPackets.S6B000233.certified) ChenEffective.PlattWindow.PointPackets.S6B000234.certified) ChenEffective.PlattWindow.PointPackets.S6B000235.certified) ChenEffective.PlattWindow.PointPackets.S6B000236.certified) ChenEffective.PlattWindow.PointPackets.S6B000237.certified) ChenEffective.PlattWindow.PointPackets.S6B000238.certified) ChenEffective.PlattWindow.PointPackets.S6B000239.certified) ChenEffective.PlattWindow.PointPackets.S6B000240.certified) ChenEffective.PlattWindow.PointPackets.S6B000241.certified) ChenEffective.PlattWindow.PointPackets.S6B000242.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0066
