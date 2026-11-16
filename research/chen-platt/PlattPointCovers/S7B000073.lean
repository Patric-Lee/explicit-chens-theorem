import PlattPointSubsetKernel
import PlattPointPackets.S3B000028
import PlattPointPackets.S3B000029
import PlattPointPackets.S3B000030
import PlattPointPackets.S3B000031
import PlattPointPackets.S3B000032
import PlattPointPackets.S3B000033
import PlattGlobalGrid.S7B000073
namespace ChenEffective.PlattWindow.PointCovers.S7B000073
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000028.points ++ ChenEffective.PlattWindow.PointPackets.S3B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000033.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000073.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000073.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000073
