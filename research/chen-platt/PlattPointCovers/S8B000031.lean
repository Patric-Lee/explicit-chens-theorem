import PlattPointSubsetKernel
import PlattPointPackets.S4B000259
import PlattPointPackets.S4B000260
import PlattPointPackets.S4B000261
import PlattPointPackets.S4B000262
import PlattPointPackets.S4B000263
import PlattPointPackets.S4B000264
import PlattPointPackets.S4B000265
import PlattPointPackets.S4B000266
import PlattPointPackets.S4B000267
import PlattPointPackets.S4B000268
import PlattGlobalGrid.S8B000031
namespace ChenEffective.PlattWindow.PointCovers.S8B000031
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000259.points ++ ChenEffective.PlattWindow.PointPackets.S4B000260.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000261.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000262.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000263.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000264.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000265.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000266.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000267.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000268.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000031.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000031.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000031
