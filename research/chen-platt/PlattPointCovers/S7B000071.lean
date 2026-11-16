import PlattPointSubsetKernel
import PlattPointPackets.S3B000017
import PlattPointPackets.S3B000018
import PlattPointPackets.S3B000019
import PlattPointPackets.S3B000020
import PlattPointPackets.S3B000021
import PlattPointPackets.S3B000022
import PlattPointPackets.S3B000023
import PlattGlobalGrid.S7B000071
namespace ChenEffective.PlattWindow.PointCovers.S7B000071
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((ChenEffective.PlattWindow.PointPackets.S3B000017.points ++ ChenEffective.PlattWindow.PointPackets.S3B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000023.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000071.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000071.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000071
