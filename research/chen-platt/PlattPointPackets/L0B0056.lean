import PlattPointPacketKernel
import PlattPointPackets.S5B000204
import PlattPointPackets.S5B000205
import PlattPointPackets.S5B000206
import PlattPointPackets.S5B000207
import PlattPointPackets.S5B000208
import PlattPointPackets.S5B000209
import PlattPointPackets.S5B000210
import PlattPointPackets.S5B000211
import PlattPointPackets.S5B000212
import PlattPointPackets.S5B000213
import PlattPointPackets.S5B000214
import PlattPointPackets.S5B000215
import PlattPointPackets.S5B000216
import PlattPointPackets.S5B000217
import PlattPointPackets.S5B000218
import PlattPointPackets.S5B000219
import PlattPointPackets.S5B000220
import PlattPointPackets.S5B000221
import PlattPointPackets.S5B000222
import PlattPointPackets.S5B000223
import PlattPointPackets.S5B000224
import PlattPointPackets.S5B000225
import PlattPointPackets.S5B000226
import PlattPointPackets.S5B000227
import PlattPointPackets.S5B000228
import PlattPointPackets.S5B000229
import PlattPointPackets.S5B000230
import PlattPointPackets.S5B000231
import PlattPointPackets.S5B000232
import PlattPointPackets.S5B000233
import PlattPointPackets.S5B000234
import PlattPointPackets.S5B000235
namespace ChenEffective.PlattWindow.PointPackets.L0B0056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000204.points ++ ChenEffective.PlattWindow.PointPackets.S5B000205.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000206.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000207.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000208.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000209.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000210.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000211.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000212.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000213.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000214.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000215.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000216.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000217.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000218.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000220.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000221.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000223.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000224.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000225.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000226.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000227.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000228.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000229.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000230.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000231.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000232.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000233.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000234.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000235.points)
theorem certified : PointChainCertificate 6102450176 110759785256368 110760171865627 6236667904 111031482481052 111031869245926 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S5B000204.certified) ChenEffective.PlattWindow.PointPackets.S5B000205.certified) ChenEffective.PlattWindow.PointPackets.S5B000206.certified) ChenEffective.PlattWindow.PointPackets.S5B000207.certified) ChenEffective.PlattWindow.PointPackets.S5B000208.certified) ChenEffective.PlattWindow.PointPackets.S5B000209.certified) ChenEffective.PlattWindow.PointPackets.S5B000210.certified) ChenEffective.PlattWindow.PointPackets.S5B000211.certified) ChenEffective.PlattWindow.PointPackets.S5B000212.certified) ChenEffective.PlattWindow.PointPackets.S5B000213.certified) ChenEffective.PlattWindow.PointPackets.S5B000214.certified) ChenEffective.PlattWindow.PointPackets.S5B000215.certified) ChenEffective.PlattWindow.PointPackets.S5B000216.certified) ChenEffective.PlattWindow.PointPackets.S5B000217.certified) ChenEffective.PlattWindow.PointPackets.S5B000218.certified) ChenEffective.PlattWindow.PointPackets.S5B000219.certified) ChenEffective.PlattWindow.PointPackets.S5B000220.certified) ChenEffective.PlattWindow.PointPackets.S5B000221.certified) ChenEffective.PlattWindow.PointPackets.S5B000222.certified) ChenEffective.PlattWindow.PointPackets.S5B000223.certified) ChenEffective.PlattWindow.PointPackets.S5B000224.certified) ChenEffective.PlattWindow.PointPackets.S5B000225.certified) ChenEffective.PlattWindow.PointPackets.S5B000226.certified) ChenEffective.PlattWindow.PointPackets.S5B000227.certified) ChenEffective.PlattWindow.PointPackets.S5B000228.certified) ChenEffective.PlattWindow.PointPackets.S5B000229.certified) ChenEffective.PlattWindow.PointPackets.S5B000230.certified) ChenEffective.PlattWindow.PointPackets.S5B000231.certified) ChenEffective.PlattWindow.PointPackets.S5B000232.certified) ChenEffective.PlattWindow.PointPackets.S5B000233.certified) ChenEffective.PlattWindow.PointPackets.S5B000234.certified) ChenEffective.PlattWindow.PointPackets.S5B000235.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0056
