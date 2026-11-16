import PlattPointPacketKernel
import PlattPointPackets.L0B0032
import PlattPointPackets.L0B0033
import PlattPointPackets.L0B0034
import PlattPointPackets.L0B0035
import PlattPointPackets.L0B0036
import PlattPointPackets.L0B0037
import PlattPointPackets.L0B0038
import PlattPointPackets.L0B0039
import PlattPointPackets.L0B0040
import PlattPointPackets.L0B0041
import PlattPointPackets.L0B0042
import PlattPointPackets.L0B0043
import PlattPointPackets.L0B0044
import PlattPointPackets.L0B0045
import PlattPointPackets.L0B0046
import PlattPointPackets.L0B0047
import PlattPointPackets.L0B0048
import PlattPointPackets.L0B0049
import PlattPointPackets.L0B0050
import PlattPointPackets.L0B0051
import PlattPointPackets.L0B0052
import PlattPointPackets.L0B0053
import PlattPointPackets.L0B0054
import PlattPointPackets.L0B0055
import PlattPointPackets.L0B0056
import PlattPointPackets.L0B0057
import PlattPointPackets.L0B0058
import PlattPointPackets.L0B0059
import PlattPointPackets.L0B0060
import PlattPointPackets.L0B0061
import PlattPointPackets.L0B0062
import PlattPointPackets.L0B0063
namespace ChenEffective.PlattWindow.PointPackets.L1B0001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.L0B0032.points ++ ChenEffective.PlattWindow.PointPackets.L0B0033.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0034.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0035.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0036.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0037.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0038.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0039.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0040.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0041.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0042.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0043.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0044.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0045.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0046.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0047.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0048.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0049.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0050.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0051.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0052.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0053.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0054.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0055.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0056.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0057.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0058.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0059.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0060.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0061.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0062.points) ++ ChenEffective.PlattWindow.PointPackets.L0B0063.points)
theorem certified : PointChainCertificate 2885419008 101243892916966 101244273995877 7174094848 112773638050141 112774025806792 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.L0B0032.certified) ChenEffective.PlattWindow.PointPackets.L0B0033.certified) ChenEffective.PlattWindow.PointPackets.L0B0034.certified) ChenEffective.PlattWindow.PointPackets.L0B0035.certified) ChenEffective.PlattWindow.PointPackets.L0B0036.certified) ChenEffective.PlattWindow.PointPackets.L0B0037.certified) ChenEffective.PlattWindow.PointPackets.L0B0038.certified) ChenEffective.PlattWindow.PointPackets.L0B0039.certified) ChenEffective.PlattWindow.PointPackets.L0B0040.certified) ChenEffective.PlattWindow.PointPackets.L0B0041.certified) ChenEffective.PlattWindow.PointPackets.L0B0042.certified) ChenEffective.PlattWindow.PointPackets.L0B0043.certified) ChenEffective.PlattWindow.PointPackets.L0B0044.certified) ChenEffective.PlattWindow.PointPackets.L0B0045.certified) ChenEffective.PlattWindow.PointPackets.L0B0046.certified) ChenEffective.PlattWindow.PointPackets.L0B0047.certified) ChenEffective.PlattWindow.PointPackets.L0B0048.certified) ChenEffective.PlattWindow.PointPackets.L0B0049.certified) ChenEffective.PlattWindow.PointPackets.L0B0050.certified) ChenEffective.PlattWindow.PointPackets.L0B0051.certified) ChenEffective.PlattWindow.PointPackets.L0B0052.certified) ChenEffective.PlattWindow.PointPackets.L0B0053.certified) ChenEffective.PlattWindow.PointPackets.L0B0054.certified) ChenEffective.PlattWindow.PointPackets.L0B0055.certified) ChenEffective.PlattWindow.PointPackets.L0B0056.certified) ChenEffective.PlattWindow.PointPackets.L0B0057.certified) ChenEffective.PlattWindow.PointPackets.L0B0058.certified) ChenEffective.PlattWindow.PointPackets.L0B0059.certified) ChenEffective.PlattWindow.PointPackets.L0B0060.certified) ChenEffective.PlattWindow.PointPackets.L0B0061.certified) ChenEffective.PlattWindow.PointPackets.L0B0062.certified) ChenEffective.PlattWindow.PointPackets.L0B0063.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L1B0001
