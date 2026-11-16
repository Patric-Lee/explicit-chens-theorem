import PlattPointSubsetKernel
import PlattPointPackets.S2B000290
import PlattPointPackets.S2B000291
import PlattPointPackets.S2B000292
import PlattPointPackets.S2B000293
import PlattPointPackets.S2B000294
import PlattPointPackets.S2B000295
import PlattGlobalGrid.S7B000063
namespace ChenEffective.PlattWindow.PointCovers.S7B000063
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000290.points ++ ChenEffective.PlattWindow.PointPackets.S2B000291.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000292.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000293.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000294.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000295.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000063.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000063.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000063
