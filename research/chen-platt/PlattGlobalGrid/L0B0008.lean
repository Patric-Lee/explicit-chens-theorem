import PlattGlobalGridKernel
import PlattGlobalGrid.S3B000020
import PlattGlobalGrid.S3B000021
import PlattGlobalGrid.S3B000022
import PlattGlobalGrid.S3B000023
import PlattGlobalGrid.S3B000024
import PlattGlobalGrid.S3B000025
import PlattGlobalGrid.S3B000026
import PlattGlobalGrid.S3B000027
import PlattGlobalGrid.S3B000028
import PlattGlobalGrid.S3B000029
import PlattGlobalGrid.S3B000030
import PlattGlobalGrid.S3B000031
import PlattGlobalGrid.S3B000032
import PlattGlobalGrid.S3B000033
import PlattGlobalGrid.S3B000034
import PlattGlobalGrid.S3B000035
import PlattGlobalGrid.S3B000036
import PlattGlobalGrid.S3B000037
import PlattGlobalGrid.S3B000038
import PlattGlobalGrid.S3B000039
import PlattGlobalGrid.S3B000040
import PlattGlobalGrid.S3B000041
import PlattGlobalGrid.S3B000042
import PlattGlobalGrid.S3B000043
import PlattGlobalGrid.S3B000044
import PlattGlobalGrid.S3B000045
import PlattGlobalGrid.S3B000046
import PlattGlobalGrid.S3B000047
import PlattGlobalGrid.S3B000048
import PlattGlobalGrid.S3B000049
import PlattGlobalGrid.S3B000050
import PlattGlobalGrid.S3B000051
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S3B000020.points ++ ChenEffective.PlattWindow.GlobalGrid.S3B000021.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000022.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000023.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000024.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000025.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000026.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000027.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000028.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000029.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000030.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000031.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000032.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000033.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000034.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000035.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000036.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000037.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000038.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000039.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000040.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000041.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000042.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000043.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000044.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000045.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000046.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000047.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000048.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000049.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000050.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000051.points)
theorem certified : GridWindowCertificate 38375680 50136064 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S3B000020.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000021.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000022.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000023.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000024.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000025.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000026.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000027.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000028.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000029.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000030.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000031.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000032.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000033.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000034.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000035.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000036.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000037.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000038.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000039.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000040.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000041.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000042.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000043.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000044.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000045.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000046.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000047.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000048.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000049.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000050.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000051.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0008
