import PlattPointSubsetKernel
import PlattPointPackets.S2B000261
import PlattPointPackets.S2B000262
import PlattPointPackets.S2B000263
import PlattPointPackets.S2B000264
import PlattPointPackets.S2B000265
import PlattPointPackets.S2B000266
import PlattGlobalGrid.S7B000057
namespace ChenEffective.PlattWindow.PointCovers.S7B000057
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000261.points ++ ChenEffective.PlattWindow.PointPackets.S2B000262.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000263.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000264.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000265.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000266.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000057.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000057.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000057
