import PlattPointPacketKernel
import PlattPointPackets.S1B000352
import PlattPointPackets.S1B000353
import PlattPointPackets.S1B000354
import PlattPointPackets.S1B000355
import PlattPointPackets.S1B000356
import PlattPointPackets.S1B000357
import PlattPointPackets.S1B000358
import PlattPointPackets.S1B000359
import PlattPointPackets.S1B000360
import PlattPointPackets.S1B000361
import PlattPointPackets.S1B000362
import PlattPointPackets.S1B000363
import PlattPointPackets.S1B000364
import PlattPointPackets.S1B000365
import PlattPointPackets.S1B000366
import PlattPointPackets.S1B000367
import PlattPointPackets.S1B000368
import PlattPointPackets.S1B000369
import PlattPointPackets.S1B000370
import PlattPointPackets.S1B000371
import PlattPointPackets.S1B000372
import PlattPointPackets.S1B000373
import PlattPointPackets.S1B000374
import PlattPointPackets.S1B000375
import PlattPointPackets.S1B000376
import PlattPointPackets.S1B000377
import PlattPointPackets.S1B000378
import PlattPointPackets.S1B000379
import PlattPointPackets.S1B000380
import PlattPointPackets.S1B000381
import PlattPointPackets.S1B000382
import PlattPointPackets.S1B000383
namespace ChenEffective.PlattWindow.PointPackets.L0B0011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S1B000352.points ++ ChenEffective.PlattWindow.PointPackets.S1B000353.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000354.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000355.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000356.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000357.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000358.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000359.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000360.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000361.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000362.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000363.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000364.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000365.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000366.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000367.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000368.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000369.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000370.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000371.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000372.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000373.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000374.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000375.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000376.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000377.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000378.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000379.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000380.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000381.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000382.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000383.points)
theorem certified : PointChainCertificate 691798016 82157485152337 82157852163514 758906880 83434495306008 83434863351033 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S1B000352.certified) ChenEffective.PlattWindow.PointPackets.S1B000353.certified) ChenEffective.PlattWindow.PointPackets.S1B000354.certified) ChenEffective.PlattWindow.PointPackets.S1B000355.certified) ChenEffective.PlattWindow.PointPackets.S1B000356.certified) ChenEffective.PlattWindow.PointPackets.S1B000357.certified) ChenEffective.PlattWindow.PointPackets.S1B000358.certified) ChenEffective.PlattWindow.PointPackets.S1B000359.certified) ChenEffective.PlattWindow.PointPackets.S1B000360.certified) ChenEffective.PlattWindow.PointPackets.S1B000361.certified) ChenEffective.PlattWindow.PointPackets.S1B000362.certified) ChenEffective.PlattWindow.PointPackets.S1B000363.certified) ChenEffective.PlattWindow.PointPackets.S1B000364.certified) ChenEffective.PlattWindow.PointPackets.S1B000365.certified) ChenEffective.PlattWindow.PointPackets.S1B000366.certified) ChenEffective.PlattWindow.PointPackets.S1B000367.certified) ChenEffective.PlattWindow.PointPackets.S1B000368.certified) ChenEffective.PlattWindow.PointPackets.S1B000369.certified) ChenEffective.PlattWindow.PointPackets.S1B000370.certified) ChenEffective.PlattWindow.PointPackets.S1B000371.certified) ChenEffective.PlattWindow.PointPackets.S1B000372.certified) ChenEffective.PlattWindow.PointPackets.S1B000373.certified) ChenEffective.PlattWindow.PointPackets.S1B000374.certified) ChenEffective.PlattWindow.PointPackets.S1B000375.certified) ChenEffective.PlattWindow.PointPackets.S1B000376.certified) ChenEffective.PlattWindow.PointPackets.S1B000377.certified) ChenEffective.PlattWindow.PointPackets.S1B000378.certified) ChenEffective.PlattWindow.PointPackets.S1B000379.certified) ChenEffective.PlattWindow.PointPackets.S1B000380.certified) ChenEffective.PlattWindow.PointPackets.S1B000381.certified) ChenEffective.PlattWindow.PointPackets.S1B000382.certified) ChenEffective.PlattWindow.PointPackets.S1B000383.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0011
