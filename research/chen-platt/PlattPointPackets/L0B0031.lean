import PlattPointPacketKernel
import PlattPointPackets.S3B000030
import PlattPointPackets.S3B000031
import PlattPointPackets.S3B000032
import PlattPointPackets.S3B000033
import PlattPointPackets.S3B000034
import PlattPointPackets.S3B000035
import PlattPointPackets.S3B000036
import PlattPointPackets.S3B000037
import PlattPointPackets.S3B000038
import PlattPointPackets.S3B000039
import PlattPointPackets.S3B000040
import PlattPointPackets.S3B000041
import PlattPointPackets.S3B000042
import PlattPointPackets.S3B000043
import PlattPointPackets.S3B000044
import PlattPointPackets.S3B000045
import PlattPointPackets.S3B000046
import PlattPointPackets.S3B000047
import PlattPointPackets.S3B000048
import PlattPointPackets.S3B000049
import PlattPointPackets.S3B000050
import PlattPointPackets.S3B000051
import PlattPointPackets.S3B000052
import PlattPointPackets.S3B000053
import PlattPointPackets.S3B000054
import PlattPointPackets.S3B000055
import PlattPointPackets.S3B000056
import PlattPointPackets.S3B000057
import PlattPointPackets.S3B000058
import PlattPointPackets.S3B000059
import PlattPointPackets.S3B000060
import PlattPointPackets.S3B000061
namespace ChenEffective.PlattWindow.PointPackets.L0B0031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S3B000030.points ++ ChenEffective.PlattWindow.PointPackets.S3B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000061.points)
theorem certified : PointChainCertificate 2751201280 100627662507767 100628043231717 2885419008 101243892916966 101244273995877 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S3B000030.certified) ChenEffective.PlattWindow.PointPackets.S3B000031.certified) ChenEffective.PlattWindow.PointPackets.S3B000032.certified) ChenEffective.PlattWindow.PointPackets.S3B000033.certified) ChenEffective.PlattWindow.PointPackets.S3B000034.certified) ChenEffective.PlattWindow.PointPackets.S3B000035.certified) ChenEffective.PlattWindow.PointPackets.S3B000036.certified) ChenEffective.PlattWindow.PointPackets.S3B000037.certified) ChenEffective.PlattWindow.PointPackets.S3B000038.certified) ChenEffective.PlattWindow.PointPackets.S3B000039.certified) ChenEffective.PlattWindow.PointPackets.S3B000040.certified) ChenEffective.PlattWindow.PointPackets.S3B000041.certified) ChenEffective.PlattWindow.PointPackets.S3B000042.certified) ChenEffective.PlattWindow.PointPackets.S3B000043.certified) ChenEffective.PlattWindow.PointPackets.S3B000044.certified) ChenEffective.PlattWindow.PointPackets.S3B000045.certified) ChenEffective.PlattWindow.PointPackets.S3B000046.certified) ChenEffective.PlattWindow.PointPackets.S3B000047.certified) ChenEffective.PlattWindow.PointPackets.S3B000048.certified) ChenEffective.PlattWindow.PointPackets.S3B000049.certified) ChenEffective.PlattWindow.PointPackets.S3B000050.certified) ChenEffective.PlattWindow.PointPackets.S3B000051.certified) ChenEffective.PlattWindow.PointPackets.S3B000052.certified) ChenEffective.PlattWindow.PointPackets.S3B000053.certified) ChenEffective.PlattWindow.PointPackets.S3B000054.certified) ChenEffective.PlattWindow.PointPackets.S3B000055.certified) ChenEffective.PlattWindow.PointPackets.S3B000056.certified) ChenEffective.PlattWindow.PointPackets.S3B000057.certified) ChenEffective.PlattWindow.PointPackets.S3B000058.certified) ChenEffective.PlattWindow.PointPackets.S3B000059.certified) ChenEffective.PlattWindow.PointPackets.S3B000060.certified) ChenEffective.PlattWindow.PointPackets.S3B000061.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0031
