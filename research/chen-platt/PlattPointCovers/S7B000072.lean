import PlattPointSubsetKernel
import PlattPointPackets.S3B000023
import PlattPointPackets.S3B000024
import PlattPointPackets.S3B000025
import PlattPointPackets.S3B000026
import PlattPointPackets.S3B000027
import PlattPointPackets.S3B000028
import PlattGlobalGrid.S7B000072
namespace ChenEffective.PlattWindow.PointCovers.S7B000072
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000023.points ++ ChenEffective.PlattWindow.PointPackets.S3B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000028.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000072.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000072.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000072
