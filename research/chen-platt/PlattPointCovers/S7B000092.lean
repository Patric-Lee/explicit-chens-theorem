import PlattPointSubsetKernel
import PlattPointPackets.S3B000136
import PlattPointPackets.S3B000137
import PlattPointPackets.S3B000138
import PlattPointPackets.S3B000139
import PlattPointPackets.S3B000140
import PlattPointPackets.S3B000141
import PlattPointPackets.S3B000142
import PlattGlobalGrid.S7B000092
namespace ChenEffective.PlattWindow.PointCovers.S7B000092
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000136.points ++ ChenEffective.PlattWindow.PointPackets.S3B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000140.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000141.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000142.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000092.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000092.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000092
