import PlattPointSubsetKernel
import PlattPointPackets.S1B000509
import PlattPointPackets.S1B000510
import PlattPointPackets.S1B000511
import PlattPointPackets.S1B000512
import PlattPointPackets.S1B000513
import PlattGlobalGrid.S6B000068
namespace ChenEffective.PlattWindow.PointCovers.S6B000068
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000509.points ++ ChenEffective.PlattWindow.PointPackets.S1B000510.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000511.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000512.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000513.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000068.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000068.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000068
