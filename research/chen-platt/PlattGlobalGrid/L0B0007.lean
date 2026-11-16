import PlattGlobalGridKernel
import PlattGlobalGrid.S2B000106
import PlattGlobalGrid.S2B000107
import PlattGlobalGrid.S2B000108
import PlattGlobalGrid.S2B000109
import PlattGlobalGrid.S2B000110
import PlattGlobalGrid.S2B000111
import PlattGlobalGrid.S2B000112
import PlattGlobalGrid.S2B000113
import PlattGlobalGrid.S2B000114
import PlattGlobalGrid.S2B000115
import PlattGlobalGrid.S2B000116
import PlattGlobalGrid.S2B000117
import PlattGlobalGrid.S3B000000
import PlattGlobalGrid.S3B000001
import PlattGlobalGrid.S3B000002
import PlattGlobalGrid.S3B000003
import PlattGlobalGrid.S3B000004
import PlattGlobalGrid.S3B000005
import PlattGlobalGrid.S3B000006
import PlattGlobalGrid.S3B000007
import PlattGlobalGrid.S3B000008
import PlattGlobalGrid.S3B000009
import PlattGlobalGrid.S3B000010
import PlattGlobalGrid.S3B000011
import PlattGlobalGrid.S3B000012
import PlattGlobalGrid.S3B000013
import PlattGlobalGrid.S3B000014
import PlattGlobalGrid.S3B000015
import PlattGlobalGrid.S3B000016
import PlattGlobalGrid.S3B000017
import PlattGlobalGrid.S3B000018
import PlattGlobalGrid.S3B000019
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S2B000106.points ++ ChenEffective.PlattWindow.GlobalGrid.S2B000107.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000108.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000109.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000110.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000111.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000112.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000113.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000114.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000115.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000116.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000117.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000000.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000001.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000002.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000003.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000004.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000005.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000006.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000007.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000008.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000009.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000010.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000011.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000012.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000013.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000014.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000015.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000016.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000017.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000018.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000019.points)
theorem certified : GridWindowCertificate 29449088 38375680 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S2B000106.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000107.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000108.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000109.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000110.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000111.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000112.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000113.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000114.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000115.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000116.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000117.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000000.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000001.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000002.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000003.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000004.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000005.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000006.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000007.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000008.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000009.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000010.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000011.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000012.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000013.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000014.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000015.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000016.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000017.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000018.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000019.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0007
