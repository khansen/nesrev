"""Admission of a client workspace independent of ambient Git configuration."""
from pathlib import Path


def require_source_free(path):
    path = Path(path).absolute()
    for spelling in (path, path.resolve()):
        for parent in (spelling, *spelling.parents):
            marker = parent / '.git'
            bare = (parent / 'HEAD').is_file() and (parent / 'objects').is_dir() and (parent / 'refs').is_dir()
            if marker.exists() or marker.is_symlink() or bare:
                raise ValueError('CLIENT_WORKSPACE_GIT_ANCESTOR')
