import PlattPointPacketKernel
import PlattPointPackets.S7B000154
import PlattPointPackets.S7B000155
import PlattPointPackets.S7B000156
import PlattPointPackets.S7B000157
import PlattPointPackets.S7B000158
import PlattPointPackets.S7B000159
import PlattPointPackets.S7B000160
import PlattPointPackets.S7B000161
import PlattPointPackets.S7B000162
import PlattPointPackets.S7B000163
import PlattPointPackets.S7B000164
import PlattPointPackets.S7B000165
import PlattPointPackets.S7B000166
import PlattPointPackets.S7B000167
import PlattPointPackets.S7B000168
import PlattPointPackets.S7B000169
import PlattPointPackets.S7B000170
import PlattPointPackets.S7B000171
import PlattPointPackets.S7B000172
import PlattPointPackets.S7B000173
import PlattPointPackets.S7B000174
import PlattPointPackets.S7B000175
import PlattPointPackets.S7B000176
import PlattPointPackets.S7B000177
import PlattPointPackets.S7B000178
import PlattPointPackets.S7B000179
import PlattPointPackets.S7B000180
import PlattPointPackets.S7B000181
import PlattPointPackets.S7B000182
import PlattPointPackets.S7B000183
import PlattPointPackets.S7B000184
import PlattPointPackets.S7B000185
namespace ChenEffective.PlattWindow.PointPackets.L0B0074
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000154.points ++ ChenEffective.PlattWindow.PointPackets.S7B000155.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000156.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000157.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000158.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000159.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000160.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000161.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000162.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000163.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000164.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000165.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000166.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000167.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000168.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000169.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000170.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000171.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000172.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000173.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000174.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000175.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000176.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000177.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000178.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000179.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000180.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000182.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000183.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000184.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000185.points)
theorem certified : PointChainCertificate 8514174976 114889767497565 114890156463719 8648392704 115082270435770 115082659513537 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000154.certified) ChenEffective.PlattWindow.PointPackets.S7B000155.certified) ChenEffective.PlattWindow.PointPackets.S7B000156.certified) ChenEffective.PlattWindow.PointPackets.S7B000157.certified) ChenEffective.PlattWindow.PointPackets.S7B000158.certified) ChenEffective.PlattWindow.PointPackets.S7B000159.certified) ChenEffective.PlattWindow.PointPackets.S7B000160.certified) ChenEffective.PlattWindow.PointPackets.S7B000161.certified) ChenEffective.PlattWindow.PointPackets.S7B000162.certified) ChenEffective.PlattWindow.PointPackets.S7B000163.certified) ChenEffective.PlattWindow.PointPackets.S7B000164.certified) ChenEffective.PlattWindow.PointPackets.S7B000165.certified) ChenEffective.PlattWindow.PointPackets.S7B000166.certified) ChenEffective.PlattWindow.PointPackets.S7B000167.certified) ChenEffective.PlattWindow.PointPackets.S7B000168.certified) ChenEffective.PlattWindow.PointPackets.S7B000169.certified) ChenEffective.PlattWindow.PointPackets.S7B000170.certified) ChenEffective.PlattWindow.PointPackets.S7B000171.certified) ChenEffective.PlattWindow.PointPackets.S7B000172.certified) ChenEffective.PlattWindow.PointPackets.S7B000173.certified) ChenEffective.PlattWindow.PointPackets.S7B000174.certified) ChenEffective.PlattWindow.PointPackets.S7B000175.certified) ChenEffective.PlattWindow.PointPackets.S7B000176.certified) ChenEffective.PlattWindow.PointPackets.S7B000177.certified) ChenEffective.PlattWindow.PointPackets.S7B000178.certified) ChenEffective.PlattWindow.PointPackets.S7B000179.certified) ChenEffective.PlattWindow.PointPackets.S7B000180.certified) ChenEffective.PlattWindow.PointPackets.S7B000181.certified) ChenEffective.PlattWindow.PointPackets.S7B000182.certified) ChenEffective.PlattWindow.PointPackets.S7B000183.certified) ChenEffective.PlattWindow.PointPackets.S7B000184.certified) ChenEffective.PlattWindow.PointPackets.S7B000185.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0074
