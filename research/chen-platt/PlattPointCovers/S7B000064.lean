import PlattPointSubsetKernel
import PlattPointPackets.S2B000295
import PlattPointPackets.S2B000296
import PlattPointPackets.S2B000297
import PlattPointPackets.S2B000298
import PlattPointPackets.S2B000299
import PlattGlobalGrid.S7B000064
namespace ChenEffective.PlattWindow.PointCovers.S7B000064
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000295.points ++ ChenEffective.PlattWindow.PointPackets.S2B000296.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000297.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000298.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000299.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000064.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000064.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000064
