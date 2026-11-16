import PlattPointPacketKernel
import PlattPointPackets.S7B000218
import PlattPointPackets.S7B000219
import PlattPointPackets.S7B000220
import PlattPointPackets.S7B000221
import PlattPointPackets.S7B000222
import PlattPointPackets.S7B000223
import PlattPointPackets.S7B000224
import PlattPointPackets.S7B000225
import PlattPointPackets.S7B000226
import PlattPointPackets.S7B000227
import PlattPointPackets.S7B000228
import PlattPointPackets.S7B000229
import PlattPointPackets.S7B000230
import PlattPointPackets.S7B000231
import PlattPointPackets.S7B000232
import PlattPointPackets.S7B000233
import PlattPointPackets.S7B000234
import PlattPointPackets.S7B000235
import PlattPointPackets.S7B000236
import PlattPointPackets.S7B000237
import PlattPointPackets.S7B000238
import PlattPointPackets.S7B000239
import PlattPointPackets.S7B000240
import PlattPointPackets.S7B000241
import PlattPointPackets.S7B000242
import PlattPointPackets.S7B000243
import PlattPointPackets.S7B000244
import PlattPointPackets.S7B000245
import PlattPointPackets.S7B000246
import PlattPointPackets.S7B000247
import PlattPointPackets.S7B000248
import PlattPointPackets.S7B000249
namespace ChenEffective.PlattWindow.PointPackets.L0B0076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000218.points ++ ChenEffective.PlattWindow.PointPackets.S7B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000220.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000221.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000223.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000224.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000225.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000226.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000227.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000228.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000229.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000230.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000231.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000232.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000233.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000234.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000235.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000236.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000237.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000238.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000239.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000240.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000241.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000242.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000243.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000244.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000245.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000246.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000247.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000248.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000249.points)
theorem certified : PointChainCertificate 8782610432 115271606006600 115271995194379 8916828160 115457996874821 115458386171407 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000218.certified) ChenEffective.PlattWindow.PointPackets.S7B000219.certified) ChenEffective.PlattWindow.PointPackets.S7B000220.certified) ChenEffective.PlattWindow.PointPackets.S7B000221.certified) ChenEffective.PlattWindow.PointPackets.S7B000222.certified) ChenEffective.PlattWindow.PointPackets.S7B000223.certified) ChenEffective.PlattWindow.PointPackets.S7B000224.certified) ChenEffective.PlattWindow.PointPackets.S7B000225.certified) ChenEffective.PlattWindow.PointPackets.S7B000226.certified) ChenEffective.PlattWindow.PointPackets.S7B000227.certified) ChenEffective.PlattWindow.PointPackets.S7B000228.certified) ChenEffective.PlattWindow.PointPackets.S7B000229.certified) ChenEffective.PlattWindow.PointPackets.S7B000230.certified) ChenEffective.PlattWindow.PointPackets.S7B000231.certified) ChenEffective.PlattWindow.PointPackets.S7B000232.certified) ChenEffective.PlattWindow.PointPackets.S7B000233.certified) ChenEffective.PlattWindow.PointPackets.S7B000234.certified) ChenEffective.PlattWindow.PointPackets.S7B000235.certified) ChenEffective.PlattWindow.PointPackets.S7B000236.certified) ChenEffective.PlattWindow.PointPackets.S7B000237.certified) ChenEffective.PlattWindow.PointPackets.S7B000238.certified) ChenEffective.PlattWindow.PointPackets.S7B000239.certified) ChenEffective.PlattWindow.PointPackets.S7B000240.certified) ChenEffective.PlattWindow.PointPackets.S7B000241.certified) ChenEffective.PlattWindow.PointPackets.S7B000242.certified) ChenEffective.PlattWindow.PointPackets.S7B000243.certified) ChenEffective.PlattWindow.PointPackets.S7B000244.certified) ChenEffective.PlattWindow.PointPackets.S7B000245.certified) ChenEffective.PlattWindow.PointPackets.S7B000246.certified) ChenEffective.PlattWindow.PointPackets.S7B000247.certified) ChenEffective.PlattWindow.PointPackets.S7B000248.certified) ChenEffective.PlattWindow.PointPackets.S7B000249.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0076
