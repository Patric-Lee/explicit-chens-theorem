import PlattPointSubsetKernel
import PlattPointPackets.S3B000066
import PlattPointPackets.S3B000067
import PlattPointPackets.S3B000068
import PlattPointPackets.S3B000069
import PlattPointPackets.S3B000070
import PlattPointPackets.S3B000071
import PlattGlobalGrid.S7B000080
namespace ChenEffective.PlattWindow.PointCovers.S7B000080
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S3B000066.points ++ ChenEffective.PlattWindow.PointPackets.S3B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000071.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000080.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000080.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000080
