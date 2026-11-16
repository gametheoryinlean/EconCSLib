import unittest
from collections import Counter

from scripts.check_efg_api_growth import (
    SurfaceEntry,
    api_growth,
    public_surface_entries,
)


class EFGApiGrowthTest(unittest.TestCase):
    def test_public_surface_excludes_private_and_local_declarations(self):
        source = """\
private theorem hidden : True := by trivial
local instance : Inhabited Nat := ⟨0⟩
theorem visible : True := by trivial
protected noncomputable def exposed : Nat := 0
instance namedInstance : Inhabited Nat := ⟨0⟩
"""

        entries = public_surface_entries(
            "EconCSLib.Example",
            "Canonical",
            source,
        )

        self.assertEqual(
            entries,
            Counter(
                {
                    SurfaceEntry(
                        "Canonical",
                        "EconCSLib.Example",
                        "theorem",
                        "visible",
                    ): 1,
                    SurfaceEntry(
                        "Canonical",
                        "EconCSLib.Example",
                        "def",
                        "exposed",
                    ): 1,
                    SurfaceEntry(
                        "Canonical",
                        "EconCSLib.Example",
                        "instance",
                        "namedInstance : Inhabited Nat",
                    ): 1,
                }
            ),
        )

    def test_api_growth_reports_new_modules_and_multiset_additions(self):
        old = SurfaceEntry(
            "Canonical",
            "EconCSLib.Existing",
            "theorem",
            "endpoint",
        )
        added = SurfaceEntry(
            "Frontend",
            "EconCSLib.New",
            "def",
            "model",
        )

        modules, declarations = api_growth(
            ["EconCSLib.Existing"],
            Counter({old: 1}),
            ["EconCSLib.Existing", "EconCSLib.New"],
            Counter({old: 2, added: 1}),
        )

        self.assertEqual(modules, ["EconCSLib.New"])
        self.assertEqual(declarations, Counter({old: 1, added: 1}))


if __name__ == "__main__":
    unittest.main()
